/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>

#include <pcap.h>
#include <rte_thash.h>

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 1024
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

static struct rte_eth_dev_tx_buffer *tx_buffer;

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */

struct hack_pkt_meta {
        uint8_t action;       /* Action to be performed */
        uint16_t destination; /* where to go next */
        uint16_t src;         /* who processed the packet last */
        uint8_t chain_index;  /*index of the current step in the service chain*/
        uint8_t flags;        /* bits for custom NF data. Use with caution to prevent collisions from different NFs. */
};

static inline struct hack_pkt_meta *
hack_get_pkt_meta(struct rte_mbuf *pkt) {
	return (struct hack_pkt_meta *)&pkt->udata64;
}

/* number of package between each print */
static uint32_t print_delay = 10000000;

/* Variables for measuring packet latency */
static uint8_t measure_latency = 0;
static uint32_t latency_packets = 0;
static uint64_t total_latency = 0;
static uint16_t destination = 0;

/* Default number of packets: 128; user can modify it by -c <packet_number> in command line */
static uint32_t packet_number = 0;
char *pcap_filename = NULL;

#define ONVM_CHECK_BIT(flags, n) !!((flags) & (1 << (n)))
#define ONVM_SET_BIT(flags, n) ((flags) | (1 << (n)))
#define SPEED_TESTER_BIT 7
#define LATENCY_BIT 6
#define ONVM_NF_ACTION_TONF 2  // send to the NF specified in the argument field (assume it is on the same host)
#define ONVM_NF_ACTION_DROP 0  // drop packet
uint16_t port_id = 0;
#define PORTID port_id
#define NUM_RX_QUEUE 1
#define NUM_TX_QUEUE 1
#define RX_QUEUE_SIZE 20000
#define TX_QUEUE_SIZE 20000

/*
 * This function displays stats. It uses ANSI terminal codes to clear
 * screen when called. It is called from a single non-master
 * thread in the server process, when the process is run with more
 * than one lcore enabled.
 */
static void
do_stats_display(struct rte_mbuf *pkt) {
        static uint64_t last_cycles;
        static uint64_t cur_pkts = 0;
        static uint64_t last_pkts = 0;
        const char clr[] = {27, '[', '2', 'J', '\0'};
        const char topLeft[] = {27, '[', '1', ';', '1', 'H', '\0'};
        (void)pkt;

        uint64_t cur_cycles = rte_get_tsc_cycles();
        cur_pkts += print_delay;

        /* Clear screen and move to top left */
        printf("%s%s", clr, topLeft);

        printf("Total packets: %9" PRIu64 " \n", cur_pkts);
        printf("TX pkts per second: %9" PRIu64 " \n",
               (cur_pkts - last_pkts) * rte_get_timer_hz() / (cur_cycles - last_cycles));
        if (measure_latency && latency_packets > 0)
                printf("Avg latency nanoseconds: %6" PRIu64 " \n",
                       total_latency / (latency_packets)*1000000000 / rte_get_timer_hz());
        printf("Initial packets created: %u\n", packet_number);

        total_latency = 0;
        latency_packets = 0;

        last_pkts = cur_pkts;
        last_cycles = cur_cycles;

        printf("\n\n");
}

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
		   "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
		   "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
		   "      When enabled:\n"
		   "       - The source MAC address is replaced by the TX port MAC address\n"
		   "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n",
	       prgname);
}

static const char short_options[] =
	"g:"  /* portmask */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
};

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{NULL, 0, 0, 0}
};

static uint8_t use_custom_pkt_count = 0;
#define MAX_PKT_NUM 16384

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		case 'g':
			use_custom_pkt_count = 1;
			packet_number = strtoul(optarg, NULL, 10);
			if (packet_number > MAX_PKT_NUM) {
					// RTE_LOG(INFO, APP, "Illegal packet number(1 ~ %u) %u!\n", MAX_PKT_NUM, packet_number);
					return -1;
			}
			break;

		/* long options */
		case 0:
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

#define IP_PROTOCOL_TCP 6
#define IP_PROTOCOL_UDP 17

struct rte_ipv4_hdr*
onvm_pkt_ipv4_hdr(struct rte_mbuf* pkt) {
        struct rte_ipv4_hdr* ipv4 =
                (struct rte_ipv4_hdr*)(rte_pktmbuf_mtod(pkt, uint8_t*) + sizeof(struct rte_ether_hdr));

        /* In an IP packet, the first 4 bits determine the version.
         * The next 4 bits are called the Internet Header Length, or IHL.
         * DPDK's ipv4_hdr struct combines both the version and the IHL into one uint8_t.
         */
        uint8_t version = (ipv4->version_ihl >> 4) & 0b1111;
        if (unlikely(version != 4)) {
                return NULL;
        }
        return ipv4;
}

int
onvm_pkt_is_ipv4(struct rte_mbuf* pkt) {
        return onvm_pkt_ipv4_hdr(pkt) != NULL;
}

struct rte_tcp_hdr*
onvm_pkt_tcp_hdr(struct rte_mbuf* pkt) {
        struct rte_ipv4_hdr* ipv4 = onvm_pkt_ipv4_hdr(pkt);

        if (unlikely(
                ipv4 ==
                NULL)) {  // Since we aren't dealing with IPv6 packets for now, we can ignore anything that isn't IPv4
                return NULL;
        }

        if (ipv4->next_proto_id != IP_PROTOCOL_TCP) {
                return NULL;
        }

        uint8_t* pkt_data =
                rte_pktmbuf_mtod(pkt, uint8_t*) + sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr);
        return (struct rte_tcp_hdr*)pkt_data;
}

struct rte_udp_hdr*
onvm_pkt_udp_hdr(struct rte_mbuf* pkt) {
        struct rte_ipv4_hdr* ipv4 = onvm_pkt_ipv4_hdr(pkt);

        if (unlikely(
                ipv4 ==
                NULL)) {  // Since we aren't dealing with IPv6 packets for now, we can ignore anything that isn't IPv4
                return NULL;
        }

        if (ipv4->next_proto_id != IP_PROTOCOL_UDP) {
                return NULL;
        }

        uint8_t* pkt_data =
                rte_pktmbuf_mtod(pkt, uint8_t*) + sizeof(struct rte_ether_hdr) + sizeof(struct rte_ipv4_hdr);
        return (struct rte_udp_hdr*)pkt_data;
}

struct onvm_ft_ipv4_5tuple {
        uint32_t src_addr;
        uint32_t dst_addr;
        uint16_t src_port;
        uint16_t dst_port;
        uint8_t proto;
};

static inline int
onvm_ft_fill_key(struct onvm_ft_ipv4_5tuple *key, struct rte_mbuf *pkt) {
        struct rte_ipv4_hdr *ipv4_hdr;
        struct rte_tcp_hdr *tcp_hdr;
        struct rte_udp_hdr *udp_hdr;

        if (unlikely(!onvm_pkt_is_ipv4(pkt))) {
                return -EPROTONOSUPPORT;
        }
        ipv4_hdr = onvm_pkt_ipv4_hdr(pkt);
        memset(key, 0, sizeof(struct onvm_ft_ipv4_5tuple));
        key->proto = ipv4_hdr->next_proto_id;
        key->src_addr = ipv4_hdr->src_addr;
        key->dst_addr = ipv4_hdr->dst_addr;
        if (key->proto == IP_PROTOCOL_TCP) {
                tcp_hdr = onvm_pkt_tcp_hdr(pkt);
                key->src_port = tcp_hdr->src_port;
                key->dst_port = tcp_hdr->dst_port;
        } else if (key->proto == IP_PROTOCOL_UDP) {
                udp_hdr = onvm_pkt_udp_hdr(pkt);
                key->src_port = udp_hdr->src_port;
                key->dst_port = udp_hdr->dst_port;
        } else {
                key->src_port = 0;
                key->dst_port = 0;
        }
        return 0;
}

uint8_t rss_symmetric_key[40] = {
    0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a,
    0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a,
    0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a, 0x6d, 0x5a,
};

/*software caculate RSS*/
static inline uint32_t
onvm_softrss(struct onvm_ft_ipv4_5tuple *key) {
	union rte_thash_tuple tuple;
	uint8_t rss_key_be[RTE_DIM(rss_symmetric_key)];
	uint32_t rss_l3l4;

	rte_convert_rss_key((uint32_t *)rss_symmetric_key, (uint32_t *)rss_key_be, RTE_DIM(rss_symmetric_key));

	tuple.v4.src_addr = rte_be_to_cpu_32(key->src_addr);
	tuple.v4.dst_addr = rte_be_to_cpu_32(key->dst_addr);
	tuple.v4.sport = rte_be_to_cpu_16(key->src_port);
	tuple.v4.dport = rte_be_to_cpu_16(key->dst_port);

	rss_l3l4 = rte_softrss_be((uint32_t *)&tuple, RTE_THASH_V4_L4_LEN, rss_key_be);

	return rss_l3l4;
}

void nf_hack_pkt() {
	pcap_filename = strdup("virtual_packet.pcap");

	uint32_t i;
	uint32_t pkts_generated;
	struct rte_mempool *pktmbuf_pool;

	pkts_generated = 0;
	pktmbuf_pool = l2fwd_pktmbuf_pool;
	if (pktmbuf_pool == NULL) {
		rte_exit(EXIT_FAILURE, "Cannot find mbuf pool!\n");
	}

	struct rte_mbuf *pkt;
	pcap_t *pcap;
	const u_char *packet;
	struct pcap_pkthdr header;
	char errbuf[PCAP_ERRBUF_SIZE];
	uint32_t max_elt_size;

	printf("Replaying %s pcap file\n", pcap_filename);

	pcap = pcap_open_offline(pcap_filename, errbuf);
	if (pcap == NULL) {
		fprintf(stderr, "Error reading pcap file: %s\n", errbuf);
		rte_exit(EXIT_FAILURE, "Cannot open pcap file\n");
	}

	packet_number = (use_custom_pkt_count ? packet_number : MAX_PKT_NUM);
	struct rte_mbuf *pkts[packet_number];

	i = 0;

	/* 
		* max_elt_size is the maximum preallocated memory size permitted for each packet, 
		* adjusted for the memory offset of the rte_mbuf struct and header/tail lengths
		*/
	
	max_elt_size = pktmbuf_pool->elt_size - sizeof(struct rte_mbuf) - pktmbuf_pool->header_size - pktmbuf_pool->trailer_size;

	// Read from file, not manager
	while (((packet = pcap_next(pcap, &header)) != NULL) && (i < packet_number)) {
		struct hack_pkt_meta *pmeta;
		struct onvm_ft_ipv4_5tuple key;

		/* Length of the packet cannot exceed preallocated storage size */
		if (header.caplen > max_elt_size) {
			continue;
		}

		pkt = rte_pktmbuf_alloc(pktmbuf_pool);
		if (pkt == NULL)
				break;

		pkt->pkt_len = header.caplen;
		pkt->data_len = header.caplen;

		/* Copy the packet into the rte_mbuf data section */
		rte_memcpy(rte_pktmbuf_mtod(pkt, char *), packet, header.caplen);

		pmeta = hack_get_pkt_meta(pkt);
		pmeta->destination = destination;
		pmeta->action = ONVM_NF_ACTION_TONF;
		pmeta->flags = ONVM_SET_BIT(0, SPEED_TESTER_BIT);

		onvm_ft_fill_key(&key, pkt);
		pkt->hash.rss = onvm_softrss(&key);

		/* Add packet to batch, and update counter */
		pkts[i++] = pkt;
		pkts_generated++;
	}

	// pkts tx burst
	for (unsigned int i = 0; i < packet_number; i++) {
		rte_eth_tx_burst(PORTID, 0, pkts, pkts_generated);
	}

	/* Exit if packets were unexpectedly not created */
	if (pkts_generated == 0 && packet_number > 0) {
		rte_exit(EXIT_FAILURE, "Failed to create packets\n");
	}

	packet_number = pkts_generated;

}

static void
l2fwd_simple_forward(struct rte_mbuf *m, unsigned portid)
{
	static uint32_t counter = 0;
	if (counter++ == print_delay) {
			do_stats_display(m);
			counter = 0;
	}

	struct hack_pkt_meta *meta = hack_get_pkt_meta(m);

	if (ONVM_CHECK_BIT(meta->flags, SPEED_TESTER_BIT)) {
			/* one of our fake pkts to forward */
			meta->destination = 1;
			meta->action = ONVM_NF_ACTION_TONF;
			if (measure_latency && ONVM_CHECK_BIT(meta->flags, LATENCY_BIT)) {
					uint64_t curtime = rte_get_tsc_cycles();
					uint64_t *oldtime = (uint64_t *)(rte_pktmbuf_mtod(m, uint8_t *) + 14);
					if (*oldtime != 0) {
							total_latency += curtime - *oldtime;
							latency_packets++;
					}
					*oldtime = curtime;
			}
	} else {
			/* Drop real incoming packets */
			meta->action = ONVM_NF_ACTION_DROP;
	}

	// After pkt action, transmit it
	rte_eth_tx_buffer(portid, 0, tx_buffer, m);
}

/* main processing loop */
static void
l2fwd_main_loop(void)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	int sent;
	unsigned lcore_id;
	uint64_t prev_tsc, diff_tsc, cur_tsc;
	unsigned j, portid, nb_rx;
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
			BURST_TX_DRAIN_US;
	struct rte_eth_dev_tx_buffer *buffer;

	prev_tsc = 0;

	lcore_id = rte_lcore_id();

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	while (!force_quit) {

		cur_tsc = rte_rdtsc();

		/*
		 * TX burst queue drain
		 */
		diff_tsc = cur_tsc - prev_tsc;
		if (unlikely(diff_tsc > drain_tsc)) {

			portid = PORTID;
			buffer = tx_buffer;

			sent = rte_eth_tx_buffer_flush(portid, 0, buffer);
			if (sent)
				port_statistics[portid].tx += sent;


			prev_tsc = cur_tsc;
		}

		/*
		 * Read packet from RX queues
		 */
		portid = PORTID;
		nb_rx = rte_eth_rx_burst(portid, 0,
						pkts_burst, MAX_PKT_BURST);

		port_statistics[portid].rx += nb_rx;

		for (j = 0; j < nb_rx; j++) {
			m = pkts_burst[j];
			rte_prefetch0(rte_pktmbuf_mtod(m, void *));
			l2fwd_simple_forward(m, portid);
		}
	}
}

static int
l2fwd_launch_one_lcore(__rte_unused void *dummy)
{
	l2fwd_main_loop();
	return 0;
}

int
main(int argc, char **argv)
{
	int ret;
	uint16_t nb_ports;
	unsigned lcore_id;
	unsigned int nb_lcores = 0;
	unsigned int nb_mbufs;

	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = l2fwd_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	nb_ports = 1;

	/* Initialize the port/queue configuration of each logical core */
	nb_mbufs = RTE_MAX(nb_ports * (nb_rxd + nb_txd + MAX_PKT_BURST +
		nb_lcores * MEMPOOL_CACHE_SIZE), 8192U);

	/* create the mbuf pool */
	l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", nb_mbufs,
		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
		rte_socket_id());
	if (l2fwd_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	ret = 0;


    // 获取第一个可用的port ID
	port_id = rte_eth_find_next(0);
    if (port_id >= RTE_MAX_ETHPORTS) {
        rte_exit(EXIT_FAILURE, "No available port found\n");
    }

	// 配置port参数
	struct rte_eth_conf port_conf = {
        .rxmode = {
            .mq_mode = ETH_MQ_RX_NONE,
        },
        .txmode = {
            .mq_mode = ETH_MQ_TX_NONE,
        },
    };
    ret = rte_eth_dev_configure(port_id, NUM_RX_QUEUE, NUM_TX_QUEUE, &port_conf);
    if (ret < 0) {
        rte_exit(EXIT_FAILURE, "Port configuration failed\n");
    }

    // 分配内存资源
    ret = rte_eth_rx_queue_setup(port_id, 0, RX_QUEUE_SIZE, rte_eth_dev_socket_id(port_id), NULL, NULL);
    if (ret < 0) {
        rte_exit(EXIT_FAILURE, "Rx queue setup failed\n");
    }
    ret = rte_eth_tx_queue_setup(port_id, 0, TX_QUEUE_SIZE, rte_eth_dev_socket_id(port_id), NULL);
    if (ret < 0) {
        rte_exit(EXIT_FAILURE, "Tx queue setup failed\n");
    }

    // 启动port
    ret = rte_eth_dev_start(port_id);
    if (ret < 0) {
        rte_exit(EXIT_FAILURE, "Port start failed\n");
    }


	// forge data packets
	nf_hack_pkt();

	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MASTER);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	printf("Bye...\n");

	return ret;
}
