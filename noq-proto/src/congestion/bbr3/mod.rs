mod max_filter;

use crate::RttEstimator;
use crate::congestion::bbr3::max_filter::MaxFilter;
use crate::congestion::{Controller, ControllerFactory, ControllerMetrics};
use crate::{Duration, Instant};
use rand::{RngExt, SeedableRng};
use rand_pcg::Pcg32;
use std::any::Any;
use std::cmp::{max, min};
use std::collections::VecDeque;
use std::sync::Arc;

/// equivalent to BBR.MaxBwFilterLen <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.10>
const MAX_BW_FILTER_LEN: usize = 2;

/// equivalent to BBR.ExtraAckedFilterLen <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.11>
const EXTRA_ACKED_FILTER_LEN: usize = 10;

/// safety mechanism to flag packets as stale within our tracking VecDeque. rounds refer to <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.1>.
/// The value of 10 rounds is picked because normally after max(kTimeThreshold * max(smoothed_rtt, latest_rtt), kGranularity) <https://datatracker.ietf.org/doc/html/rfc9002#section-6.1.2>
/// the packet should have been declared lost already, this is just to guarantee that the VecDeque doesn't grow indefinitely.
const ROUND_COUNT_WINDOW: u64 = 10;

/// the minimum for the maximum datagram size <https://datatracker.ietf.org/doc/html/rfc9000#section-14>
const MIN_MAX_DATAGRAM_SIZE: u16 = 1200;

/// the maximum for the maximum datagram size <https://datatracker.ietf.org/doc/html/rfc9000#section-18.2>
const MAX_DATAGRAM_SIZE: u64 = 65527;

/// 1.2Mbps in bytes/sec used to determine send_quantum
/// this is the pacing rate used where we don't authorize a burst bigger than a full packet
/// inspired by a previous version of BBR2 used in cloudflare's quiche
const PACING_RATE_1_2MBPS: f64 = 1200.0 * 1000.0;

/// 24Mbps in bytes/sec
/// this is the pacing rate used where we don't authorize a burst bigger than two full packets
/// inspired by a previous version of BBR2 used in cloudflare's quiche
const PACING_RATE_24MBPS: f64 = 24000.0 * 1000.0;

/// 64 Kb in bytes
/// this is the maximum size we want for a quantum in `set_send_quantum`
/// inspired by a previous version of BBR2 used in cloudflare's quiche
const HIGH_PACE_MAX_QUANTUM: u64 = 64 * 1000;

/// equivalent to BBR.StartupPacingGain: A constant specifying the minimum gain value for calculating the pacing rate that will allow
/// the sending rate to double each round (4 * ln(2) ~= 2.77)
/// BBRStartupPacingGain; used in Startup mode for BBR.pacing_gain. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const STARTUP_PACING_GAIN: f64 = 2.773;

/// default pacing gain is 1, when cruising, probing for RTT or refilling <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const DEFAULT_PACING_GAIN: f64 = 1.0;

/// pacing gain when probing bandwidth down <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const PROBE_BW_DOWN_PACING_GAIN: f64 = 0.9;

/// pacing gain when probing bandwidth up <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const PROBE_BW_UP_PACING_GAIN: f64 = 1.25;

/// equivalent to BBR.PacingMarginPercent: The static discount factor of 1% used to scale BBR.bw to produce C.pacing_rate.
const PACING_MARGIN_PERCENT: f64 = 1.0;

/// equivalent to BBR.DefaultCwndGain: A constant specifying the minimum gain value that allows the sending rate to double each round (2) BBRStartupCwndGain.
/// Used by default in most phases for BBR.cwnd_gain.
const DEFAULT_CWND_GAIN: f64 = 2.0;

/// equivalent to BBR.DrainPacingGain: A constant specifying the pacing gain value used in Drain mode,
/// to attempt to drain the estimated queue at the bottleneck link in one round-trip or less.
/// As noted in BBRDrainPacingGain, any value at or below 1 / BBRStartupCwndGain = 1 / 2 = 0.5 will theoretically achieve this.
/// BBR uses the value 0.5, which has been shown to offer good performance when compared with other alternatives.
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.4>
/// <https://github.com/google/bbr/blob/master/Documentation/startup/gain/analysis/bbr_drain_gain.pdf>
const DRAIN_PACING_GAIN: f64 = 1.0 / DEFAULT_CWND_GAIN;

/// cwnd gain used when probing up <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const PROBE_BW_UP_CWND_GAIN: f64 = 2.25;

/// cwnd gain used when probing RTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
const PROBE_RTT_CWND_GAIN: f64 = 0.5;

/// equivalent to BBR.ProbeRTTDuration: A constant specifying the minimum duration for which ProbeRTT state holds C.inflight to BBR.MinPipeCwnd or fewer packets: 200 ms.
const PROBE_RTT_DURATION_MS: u64 = 200;

/// equivalent to BBR.ProbeRTTInterval: A constant specifying the minimum time interval between ProbeRTT states: 5 secs.
const PROBE_RTT_INTERVAL_SEC: u64 = 5;

/// equivalent to BBR.LossThresh: A constant specifying the maximum tolerated per-round-trip packet loss rate when probing for bandwidth (the default is 2%).
const LOSS_THRESH: f64 = 0.02;

/// equivalent to BBR.Beta: A constant specifying the default multiplicative decrease to make upon each round trip during which the connection detects packet loss (the value is 0.7).
const BETA: f64 = 0.7;

/// equivalent to BBR.Headroom: A constant specifying the multiplicative factor to apply to BBR.inflight_longterm when calculating
/// a volume of free headroom to try to leave unused in the path
/// (e.g. free space in the bottleneck buffer or free time slots in the bottleneck link) that can be used by cross traffic (the value is 0.15).
const HEADROOM: f64 = 0.15;

/// equivalent to BBR.MinRTTFilterLen: A constant specifying the length of the BBR.min_rtt min filter window, BBR.MinRTTFilterLen is 10 secs.
const MIN_RTT_FILTER_LEN: u64 = 10;

/// multiplier used to check growth when validating if the full bandwidth has been reached
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.2-6>
const FULL_BW_GROWTH: f64 = 1.25;

/// maximum number of rounds needed before we consider that the pipe is full <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.2-6>
const MAX_FULL_BW_COUNT: u64 = 3;

/// equivalent to BBRStartupFullLossCnt: the minimum number of discontiguous loss
/// events observed within a single round trip before the STARTUP high-loss
/// estimator is allowed to exit STARTUP.
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#section-5.3.1.3>
const STARTUP_FULL_LOSS_CNT: u64 = 6;

/// when setting `bw_probe_up_rounds` when raising our inflight long term slope we don't go above this
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
const MAX_LONG_TERM_PROBE_UP_ROUNDS: u32 = 30;

/// max number of rounds used when deciding to coexist with Reno / CUBIC <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.1>
const MAX_RENO_ROUNDS: u64 = 63;

/// minimum amount of time to wait before probing again <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-5>
const MIN_PROBE_WAIT_MS: u64 = 2000;

/// when waiting before probing again we add up to one second of added wait time
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-5>
const MAX_ADDED_PROBE_WAIT_MS: u64 = 1000;

/// Substates when probing bandwidth
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3>
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ProbeBwSubstate {
    /// Deceleration: sends slower than delivery rate to reduce queue
    /// equivalent to ProbeBW_DOWN <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.1>
    Down,

    /// Cruising: sends at delivery rate to maintain high utilization
    /// equivalent to ProbeBW_CRUISE <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.2>
    Cruise,

    /// Refill: sends at BBR.bw for one RTT to fill pipe before probing up
    /// equivalent to ProbeBW_REFILL <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.3>
    Refill,

    /// Acceleration: sends faster than delivery rate to probe for more bandwidth
    /// equivalent to ProbeBW_UP <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.4>
    Up,
}

/// State Machine description from BBR3
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3>
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum BbrState {
    /// Initial state: rapidly probes for bandwidth using high pacing_gain
    /// equivalent to Startup <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1>
    Startup,

    /// Drains queue created during Startup by using low pacing_gain (< 1.0)
    /// equivalent to Drain <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.2>
    Drain,

    /// Steady-state phase that cycles through bandwidth probing tactics
    /// equivalent to ProbeBW states <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3>
    ProbeBw(ProbeBwSubstate),

    /// Temporarily reduces inflight to measure true min_rtt
    /// equivalent to ProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4>
    ProbeRtt,
}

/// Ack phases used during ProbeBW states
/// equivalent to BBR.ack_phase states <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6>
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum AckPhase {
    /// equivalent to ACKS_PROBE_STARTING
    ProbeStarting,
    /// equivalent to ACKS_PROBE_STOPPING
    ProbeStopping,
    /// equivalent to ACKS_REFILLING
    Refilling,
    /// equivalent to ACKS_PROBE_FEEDBACK
    ProbeFeedback,
}

/// Description of a packet for the purposes of analysis through BBR3
/// all volumes of data use bytes, all rates of data use bytes/sec
/// equivalent to P <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-4.1.2.1.2>
#[derive(Debug, Clone, Copy)]
struct BbrPacket {
    /// equivalent to P.delivered: C.delivered when the packet was sent from transport connection C.
    delivered: u64,
    /// equivalent to P.delivered_time: C.delivered_time when the packet was sent.
    delivered_time: Instant,
    /// equivalent to P.first_send_time: C.first_send_time when the packet was sent.
    first_send_time: Instant,
    /// equivalent to P.send_time: The pacing departure time selected when the packet was scheduled to be sent.
    send_time: Instant,
    /// equivalent to P.is_app_limited: true if C.app_limited was non-zero when the packet was sent, else false.
    is_app_limited: bool,
    /// equivalent to P.tx_in_flight: C.inflight immediately after the transmission of packet P.
    tx_in_flight: u64,
    /// packet number from the connection
    packet_number: u64,
    /// packet size in bytes
    size: u16,
    /// equivalent to P.lost: C.lost when the packet was sent
    lost: u64,
    /// used to flag acknowledgement within our VecDeque, a packet can be flagged lost after having been flagged acknowledged
    /// hence the necessity of this flag being set before we remove it from packets.
    acknowledged: bool,
    /// once a packet has been acknowledged on a given round it is marked for removal on the next round.
    stale: bool,
    /// used to mark packets stale if they're far from the current round <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.1>
    round_count: u64,
}

/// Description of a per-ack rate sample state that will allow us to determine a short term evolution of the connection
/// equivalent to RS <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.2>
#[derive(Debug, Clone, Copy)]
struct BbrRateSample {
    /// equivalent to RS.delivery_rate: The delivery rate (aka bandwidth) sample obtained from the packet that has just been ACKed.
    delivery_rate: f64,
    /// equivalent to RS.is_app_limited: The P.is_app_limited from the most recent packet
    ///    delivered; indicates whether the rate sample is application-limited.
    is_app_limited: bool,
    /// equivalent to RS.interval: The length of the sampling interval.
    interval: Duration,
    /// equivalent to RS.delivered: The volume of data delivered between the transmission of the packet that has just been ACKed and the current time.
    delivered: u64,
    /// equivalent to RS.prior_delivered: The P.delivered count from the most recent packet delivered.
    prior_delivered: u64,
    /// equivalent to RS.prior_time: The P.delivered_time from the most recent packet delivered.
    prior_time: Instant,
    /// equivalent to RS.send_elapsed: Send time interval calculated from the most recent
    ///    packet delivered (see the "Send Rate" section above).
    send_elapsed: Duration,
    /// equivalent to RS.ack_elapsed: ACK time interval calculated from the most recent
    ///    packet delivered (see the "ACK Rate" section above).
    ack_elapsed: Duration,
    /// equivalent to RS.rtt: The RTT sample calculated based on the most recently-sent packet of the packets that have just been ACKed.
    rtt: Duration,
    /// equivalent to RS.tx_in_flight: C.inflight at the time of the transmission of the packet that has just been ACKed
    /// (the most recently sent packet among packets ACKed by the ACK that was just received).
    tx_in_flight: u64,
    /// equivalent to RS.newly_acked: The volume of data in bytes cumulatively or selectively acknowledged upon the ACK that was just received.
    newly_acked: u64,
    /// equivalent to RS.newly_lost: The volume of data in bytes newly marked lost upon the ACK that was just received.
    newly_lost: u64,
    /// equivalent to RS.lost: The volume of data in bytes that was declared lost between the transmission
    /// and acknowledgment of the packet that has just been ACKed (the most recently sent packet among packets ACKed by the ACK that was just received).
    lost: u64,
    /// equivalent to RS.last_end_seq
    last_end_seq: u64,
    /// represents the last packet that was used in the generation of this rate sample
    last_packet: BbrPacket,
}

/// Experimental! Use at your own risk.
///
/// Aims for reduced buffer bloat and improved performance over high bandwidth-delay product networks.
/// Based on <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html>
/// equivalent to a combination of BBR and C states
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.4>
/// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.1>
#[derive(Debug, Clone)]
pub struct Bbr3 {
    /// equivalent to C.SMSS The Sender Maximum Send Size in bytes. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.1>
    /// <https://www.rfc-editor.org/rfc/rfc9000#name-datagram-size>
    smss: u64,
    /// equivalent to C.InitialCwnd: The initial congestion window set by the transport protocol implementation for the connection at initialization time.
    initial_cwnd: u64,
    /// equivalent to C.delivered: The total amount of data delivered so far over the lifetime of the transport connection C.
    /// This MUST NOT include pure ACK packets. It SHOULD include spurious retransmissions that have been acknowledged as delivered.
    delivered: u64,
    /// equivalent to C.inflight: The connection's best estimate of the number of bytes outstanding in the network.
    /// This includes the number of bytes that have been sent and have not been acknowledged or marked as lost since their last transmission
    /// (e.g. "pipe" from RFC6675 or "bytes_in_flight" from RFC9002). This MUST NOT include pure ACK packets.
    inflight: u64,
    /// equivalent to C.is_cwnd_limited: True if the connection has fully utilized C.cwnd at any point in the last packet-timed round trip.
    is_cwnd_limited: bool,
    /// equivalent to BBR.cycle_count: The virtual time used by the BBR.max_bw filter window.
    /// since the BBR.max_bw_filter only needs to track samples from two time slots: the previous ProbeBW cycle and the current ProbeBW cycle.
    cycle_count: u64,
    /// equivalent to C.cwnd: The transport sender's congestion window. When transmitting data, the sending connection ensures that C.inflight does not exceed C.cwnd.
    cwnd: u64,
    /// equivalent to C.pacing_rate: The current pacing rate for a BBR flow, which controls inter-packet spacing.
    pacing_rate: f64,
    /// equivalent to C.send_quantum: The maximum size of a data aggregate scheduled and transmitted together as a unit, e.g., to amortize per-packet transmission overheads.
    send_quantum: u64,
    /// equivalent to BBR.pacing_gain: The dynamic gain factor used to scale BBR.bw to produce C.pacing_rate.
    pacing_gain: f64,
    /// default pacing gain is 1, when cruising, probing for RTT or refilling <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    default_pacing_gain: f64,
    /// pacing gain when probing bandwidth down <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    probe_bw_down_pacing_gain: f64,
    /// pacing gain when probing bandwidth up <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    probe_bw_up_pacing_gain: f64,
    /// equivalent to BBR.StartupPacingGain: A constant specifying the minimum gain value for calculating the pacing rate that will allow
    /// the sending rate to double each round (4 * ln(2) ~= 2.77)
    /// BBRStartupPacingGain; used in Startup mode for BBR.pacing_gain. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    startup_pacing_gain: f64,
    /// equivalent to BBR.DrainPacingGain: A constant specifying the pacing gain value used in Drain mode,
    /// to attempt to drain the estimated queue at the bottleneck link in one round-trip or less.
    /// As noted in BBRDrainPacingGain, any value at or below 1 / BBRStartupCwndGain = 1 / 2 = 0.5 will theoretically achieve this.
    /// BBR uses the value 0.5, which has been shown to offer good performance when compared with other alternatives.
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    drain_pacing_gain: f64,
    /// equivalent to BBR.PacingMarginPercent: The static discount factor of 1% used to scale BBR.bw to produce C.pacing_rate.
    pacing_margin_percent: f64,
    /// equivalent to BBR.cwnd_gain: The dynamic gain factor used to scale the estimated BDP to produce a congestion window (C.cwnd).
    cwnd_gain: f64,
    /// equivalent to BBR.DefaultCwndGain: A constant specifying the minimum gain value that allows the sending rate to double each round (2) BBRStartupCwndGain.
    /// Used by default in most phases for BBR.cwnd_gain.
    default_cwnd_gain: f64,
    /// used to generate random numbers when deciding how long to wait before probing again
    /// using Pcg32 as it's a fast general purpose random number generator and fits our purpose here
    /// these numbers will not be security critical as they're only used to decide when to probe the connection next.
    probe_rng: Pcg32,
    /// cwnd gain used when probing up <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    probe_bw_up_cwnd_gain: f64,
    /// cwnd gain used when probing RTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.1>
    probe_rtt_cwnd_gain: f64,
    /// equivalent to BBR.state: The current state of a BBR flow in the BBR state machine. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-3.3>
    state: BbrState,
    /// equivalent to BBR.undo_state: The state of a BBR flow in the BBR state machine saved in case a loss episode is later declared spurious. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-3.3>
    undo_state: BbrState,
    /// equivalent to BBR.round_count: Count of packet-timed round trips elapsed so far.
    round_count: u64,
    /// equivalent to BBR.round_start: A boolean that BBR sets to true once per packet-timed round trip, on ACKs that advance BBR.round_count.
    round_start: bool,
    /// equivalent to BBR.next_round_delivered: P.delivered value denoting the end of a packet-timed round trip.
    next_round_delivered: u64,
    /// equivalent to BBR.idle_restart: A boolean that is true if and only if a connection is restarting after being idle.
    idle_restart: bool,
    /// equivalent to BBR.MinPipeCwnd: The minimal C.cwnd value BBR targets, to allow pipelining with endpoints that follow an "ACK every other packet" delayed-ACK policy: 4 * C.SMSS.
    min_pipe_cwnd: u64,
    /// equivalent to BBR.max_bw: The windowed maximum recent bandwidth sample, obtained using the BBR delivery rate sampling algorithm in
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-4.1>,
    /// measured during the current or previous bandwidth probing cycle (or during Startup, if the flow is still in that state). (Part of the long-term model.)
    max_bw: f64,
    /// equivalent to BBR.bw_shortterm: The short-term maximum sending bandwidth that the algorithm estimates is safe for matching the current network path delivery rate,
    /// based on any loss signals in the current bandwidth probing cycle. This is generally lower than max_bw. (Part of the short-term model.)
    bw_shortterm: f64,
    /// equivalent to BBR.undo_bw_shortterm: The short-term maximum sending bandwidth that the algorithm estimates is safe for matching the current network path delivery rate,
    /// based on any loss signals in the current bandwidth probing cycle. This is generally lower than max_bw. (Part of the short-term model.)
    /// saved state in case a loss episode is later declared spurious
    undo_bw_shortterm: f64,
    /// equivalent to BBR.bw: The maximum sending bandwidth that the algorithm estimates is appropriate for matching the current network path delivery rate,
    /// given all available signals in the model, at any time scale. It is the min() of max_bw and bw_shortterm.
    bw: f64,
    /// equivalent to BBR.min_rtt: The windowed minimum round-trip time sample measured over the last BBR.MinRTTFilterLen = 10 seconds.
    /// This attempts to estimate the two-way propagation delay of the network path when all connections sharing a bottleneck are using BBR,
    /// but also allows BBR to estimate the value required for a BBR.bdp estimate that allows full throughput if there are legacy loss-based Reno or CUBIC flows sharing the bottleneck.
    min_rtt: Duration,
    /// equivalent to BBR.bdp: The estimate of the network path's BDP (Bandwidth-Delay Product), computed as: BBR.bdp = BBR.bw * BBR.min_rtt.
    bdp: u64,
    /// equivalent to BBR.extra_acked: A volume of data that is the estimate of the recent degree of aggregation in the network path.
    extra_acked: u64,
    /// equivalent to BBR.offload_budget: The estimate of the minimum volume of data necessary to achieve full throughput when using sender
    /// (TSO/GSO) and receiver (LRO, GRO) host offload mechanisms.
    offload_budget: u64,
    /// equivalent to BBR.max_inflight: The estimate of C.inflight required to fully utilize the bottleneck bandwidth available to the flow,
    /// based on the BDP estimate (BBR.bdp), the aggregation estimate (BBR.extra_acked), the offload budget (BBR.offload_budget), and BBR.MinPipeCwnd.
    max_inflight: u64,
    /// equivalent to BBR.inflight_longterm: The long-term maximum inflight that the algorithm estimates will produce acceptable queue pressure,
    /// based on signals in the current or previous bandwidth probing cycle, as measured by loss. That is, if a flow is probing for bandwidth,
    /// and observes that sending a particular inflight causes a loss rate higher than the loss rate threshold,
    /// it sets inflight_longterm to that volume of data. (Part of the long-term model.)
    inflight_longterm: u64,
    /// equivalent to BBR.inflight_longterm: The long-term maximum inflight that the algorithm estimates will produce acceptable queue pressure,
    /// based on signals in the current or previous bandwidth probing cycle, as measured by loss. That is, if a flow is probing for bandwidth,
    /// and observes that sending a particular inflight causes a loss rate higher than the loss rate threshold,
    /// it sets inflight_longterm to that volume of data. (Part of the long-term model.)
    /// saved state in case a loss episode is later declared spurious
    undo_inflight_longterm: u64,
    /// equivalent to BBR.inflight_shortterm: Analogous to BBR.bw_shortterm,
    /// the short-term maximum inflight that the algorithm estimates is safe for matching the current network path delivery process,
    /// based on any loss signals in the current bandwidth probing cycle. This is generally lower than max_inflight or inflight_longterm. (Part of the short-term model.)
    inflight_shortterm: u64,
    /// equivalent to BBR.undo_inflight_shortterm: Analogous to BBR.bw_shortterm,
    /// the short-term maximum inflight that the algorithm estimates is safe for matching the current network path delivery process,
    /// based on any loss signals in the current bandwidth probing cycle. This is generally lower than max_inflight or inflight_longterm. (Part of the short-term model.)
    /// saved state in case a loss episode is later declared spurious
    undo_inflight_shortterm: u64,
    /// equivalent to BBR.bw_latest: a 1-round-trip max of delivered bandwidth (RS.delivery_rate).
    bw_latest: f64,
    /// equivalent to BBR.inflight_latest: a 1-round-trip max of delivered volume of data (RS.delivered).
    inflight_latest: u64,
    /// equivalent to BBR.max_bw_filter: A windowed max filter for RS.delivery_rate samples, for estimating BBR.max_bw.
    max_bw_filter: MaxFilter,
    /// equivalent to BBR.extra_acked_interval_start: The start of the time interval for estimating the excess amount of data acknowledged due to aggregation effects.
    extra_acked_interval_start: Option<Instant>,
    /// equivalent to BBR.extra_acked_delivered: The volume of data marked as delivered since BBR.extra_acked_interval_start.
    extra_acked_delivered: u64,
    /// equivalent to BBR.extra_acked_filter: A windowed max filter for tracking the degree of aggregation in the path.
    extra_acked_filter: MaxFilter,
    /// equivalent to BBR.full_bw_reached: A boolean that records whether BBR estimates that it has ever fully utilized its available bandwidth over the lifetime of the connection.
    full_bw_reached: bool,
    /// equivalent to BBR.full_bw_now: A boolean that records whether BBR estimates that it has fully utilized its available bandwidth since it most recetly started looking.
    full_bw_now: bool,
    /// equivalent to BBR.full_bw: A recent baseline BBR.max_bw to estimate if BBR has "filled the pipe" in Startup.
    full_bw: f64,
    /// equivalent to BBR.full_bw_count: The number of non-app-limited round trips without large increases in BBR.full_bw.
    full_bw_count: u64,
    /// equivalent to BBR.min_rtt_stamp: The wall clock time at which the current BBR.min_rtt sample was obtained.
    min_rtt_stamp: Option<Instant>,
    /// equivalent to BBR.ProbeRTTDuration: A constant specifying the minimum duration for which ProbeRTT state holds C.inflight to BBR.MinPipeCwnd or fewer packets: 200 ms.
    probe_rtt_duration: Duration,
    /// equivalent to BBR.ProbeRTTInterval: A constant specifying the minimum time interval between ProbeRTT states: 5 secs.
    probe_rtt_interval: Duration,
    /// equivalent to BBR.probe_rtt_min_delay: The minimum RTT sample recorded in the last ProbeRTTInterval.
    probe_rtt_min_delay: Duration,
    /// equivalent to BBR.probe_rtt_min_stamp: The wall clock time at which the current BBR.probe_rtt_min_delay sample was obtained.
    probe_rtt_min_stamp: Option<Instant>,
    /// equivalent to BBR.probe_rtt_expired: A boolean recording whether the BBR.probe_rtt_min_delay has expired and
    /// is due for a refresh with an application idle period or a transition into ProbeRTT state.
    probe_rtt_expired: bool,
    /// equivalent to C.delivered_time: The wall clock time when C.delivered was last updated. <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-4.1.1.2.1>
    delivered_time: Option<Instant>,
    /// equivalent to C.first_send_time: If packets are in flight, then this holds the send time of the packet that was most recently marked as delivered.
    /// Else, if the connection was recently idle, then this holds the send time of most recently sent packet.
    first_send_time: Option<Instant>,
    /// equivalent to C.app_limited: The index of the last transmitted packet marked as application-limited, or 0 if the connection is not currently application-limited.
    app_limited: u64,
    /// equivalent to C.lost: the number of bytes that have been lost during the lifetime of this connection
    lost: u64,
    /// equivalent to C.srtt: The smoothed RTT, an exponentially weighted moving average of the observed RTT of the connection.
    srtt: Duration,
    /// collection of packets in flight or just acknowledged / lost.
    packets: VecDeque<BbrPacket>,
    /// equivalent to RS: Per-ACK Rate Sample State <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.2>
    rs: Option<BbrRateSample>,
    /// equivalent to BBR.rounds_since_bw_probe: rounds since last bw probe state.
    rounds_since_bw_probe: u64,
    /// equivalent to BBR.bw_probe_wait: random wait time before entering probing state again
    bw_probe_wait: Duration,
    /// equivalent to BBR.bw_probe_up_rounds: number of rounds that have been executed in probe up state
    bw_probe_up_rounds: u32,
    /// equivalent to BBR.bw_probe_up_acks: volume of data in bytes that has been acknowledged during probe up state
    bw_probe_up_acks: u64,
    /// equivalent to BBR.probe_up_cnt: count of the number of times we've grown the cwnd during probe up state
    probe_up_cnt: u64,
    /// equivalent to BBR.cycle_stamp: timestamp when we start probing down state
    cycle_stamp: Option<Instant>,
    /// equivalent to BBR.ack_phase: ACK phase during probing states
    ack_phase: AckPhase,
    /// equivalent to BBR.bw_probe_samples: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2>
    bw_probe_samples: bool,
    /// equivalent to BBR.loss_round_delivered: C.delivered during the first loss of the round
    loss_round_delivered: u64,
    /// equivalent to BBR.loss_in_round: flag set to true when loss occurs during the round
    loss_in_round: bool,
    /// equivalent to BBR.loss_events_in_round: count of discontiguous loss events
    /// observed in the current round trip, used by the STARTUP high-loss exit
    /// (BBRStartupFullLossCnt criterion). Reset at each loss-round boundary.
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#section-5.3.1.3>
    loss_events_in_round: u64,
    /// equivalent to BBR.probe_rtt_done_stamp: timestamp when probe RTT state is finished
    probe_rtt_done_stamp: Option<Instant>,
    /// equivalent to BBR.probe_rtt_round_done: set once per round when BBR.probe_rtt_done_stamp to check if we need to switch state
    probe_rtt_round_done: bool,
    /// equivalent to BBR.prior_cwnd: cwnd from last round
    prior_cwnd: u64,
    /// equivalent to BBR.loss_round_start: flag set to true at the very beginning of a round where loss occurred
    loss_round_start: bool,
    /// equivalent to BBR.drain_start_round: The value of round_count when Drain state started.
    drain_start_round: u64,
    /// Number of ack-eliciting packets the peer may receive before sending an immediate ACK,
    /// as requested via the QUIC ACK frequency extension. Used when computing `offload_budget`
    /// per <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.8.2>.
    ack_eliciting_threshold: u64,
    /// `max_ack_delay` we requested the peer to use via the QUIC ACK frequency extension.
    /// Used when computing `offload_budget` per
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.8.2>.
    max_ack_delay: Duration,
}

impl Bbr3 {
    fn new(config: Arc<Bbr3Config>, current_mtu: u16) -> Self {
        let probe_rng: Pcg32;
        if let Some(probe_seed) = config.probe_rng_seed {
            probe_rng = Pcg32::from_seed(probe_seed);
        } else {
            probe_rng = Pcg32::from_rng(&mut rand::rng());
        }
        let smss = min(
            max(MIN_MAX_DATAGRAM_SIZE, current_mtu) as u64,
            MAX_DATAGRAM_SIZE,
        );
        let initial_cwnd = config.initial_window;
        let startup_pacing_gain = config.startup_pacing_gain.unwrap_or(STARTUP_PACING_GAIN);
        let default_pacing_gain = config.default_pacing_gain.unwrap_or(DEFAULT_PACING_GAIN);
        let probe_bw_down_pacing_gain = config
            .probe_bw_down_pacing_gain
            .unwrap_or(PROBE_BW_DOWN_PACING_GAIN);
        let probe_bw_up_pacing_gain = config
            .probe_bw_up_pacing_gain
            .unwrap_or(PROBE_BW_UP_PACING_GAIN);
        let drain_pacing_gain = config.drain_pacing_gain.unwrap_or(DRAIN_PACING_GAIN);
        let pacing_margin_percent = config
            .pacing_margin_percent
            .unwrap_or(PACING_MARGIN_PERCENT);
        let default_cwnd_gain = config.default_cwnd_gain.unwrap_or(DEFAULT_CWND_GAIN);
        let probe_bw_up_cwnd_gain = config
            .probe_bw_up_cwnd_gain
            .unwrap_or(PROBE_BW_UP_CWND_GAIN);
        let probe_rtt_cwnd_gain = config.probe_rtt_cwnd_gain.unwrap_or(PROBE_RTT_CWND_GAIN);
        // the calculation for initial pacing rate described here <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.2-5>
        let nominal_bandwidth = initial_cwnd as f64 / 0.001;
        let pacing_rate = startup_pacing_gain * nominal_bandwidth;
        Self {
            smss,
            initial_cwnd,
            delivered: 0,
            inflight: 0,
            is_cwnd_limited: false,
            cycle_count: 0,
            cwnd: initial_cwnd,
            pacing_rate,
            send_quantum: 2 * smss, // we start high, but it will be adjusted in set_send_quantum <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.3>
            pacing_gain: startup_pacing_gain,
            startup_pacing_gain,
            default_pacing_gain,
            probe_bw_down_pacing_gain,
            probe_bw_up_pacing_gain,
            drain_pacing_gain,
            pacing_margin_percent,
            cwnd_gain: default_cwnd_gain,
            default_cwnd_gain,
            probe_rng,
            probe_bw_up_cwnd_gain,
            state: BbrState::Startup,
            undo_state: BbrState::Startup,
            round_count: 0,
            round_start: true,
            next_round_delivered: 0,
            idle_restart: false,
            min_pipe_cwnd: 4 * smss, // 4 * C.SMSS as defined in <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-2.7-4>
            max_bw: 0.0,
            bw_shortterm: f64::INFINITY,
            undo_bw_shortterm: f64::INFINITY,
            bw: 0.0,
            min_rtt: Duration::from_secs(u64::MAX),
            bdp: 0,
            extra_acked: 0,
            offload_budget: 0,
            max_inflight: 0,
            inflight_longterm: u64::MAX,
            undo_inflight_longterm: u64::MAX,
            inflight_shortterm: u64::MAX,
            undo_inflight_shortterm: u64::MAX,
            bw_latest: 0.0,
            inflight_latest: 0,
            max_bw_filter: MaxFilter::new(MAX_BW_FILTER_LEN as u64),
            extra_acked_interval_start: None,
            extra_acked_delivered: 0,
            extra_acked_filter: MaxFilter::new(EXTRA_ACKED_FILTER_LEN as u64),
            full_bw_reached: false,
            full_bw_now: false,
            full_bw: 0.0,
            full_bw_count: 0,
            min_rtt_stamp: None,
            probe_rtt_cwnd_gain,
            probe_rtt_duration: Duration::from_millis(PROBE_RTT_DURATION_MS),
            probe_rtt_interval: Duration::from_secs(PROBE_RTT_INTERVAL_SEC),
            probe_rtt_min_delay: Duration::ZERO,
            probe_rtt_min_stamp: None,
            probe_rtt_expired: false,
            delivered_time: None,
            first_send_time: None,
            app_limited: 0,
            lost: 0,
            srtt: Duration::ZERO,
            rs: None,
            packets: VecDeque::new(),
            rounds_since_bw_probe: 0,
            bw_probe_wait: Duration::ZERO,
            bw_probe_up_rounds: 0,
            bw_probe_up_acks: 0,
            probe_up_cnt: 0,
            cycle_stamp: None,
            ack_phase: AckPhase::ProbeStarting,
            bw_probe_samples: false,
            loss_events_in_round: 0,
            loss_round_delivered: 0,
            loss_in_round: false,
            probe_rtt_done_stamp: None,
            probe_rtt_round_done: false,
            prior_cwnd: 0,
            loss_round_start: false,
            drain_start_round: 0,
            // Conservative defaults that match RFC 9000 §13.2.2 behavior (ACK every other
            // ack-eliciting packet) and the default QUIC `max_ack_delay` of 25ms. Overridden
            // when the connection supplies peer ACK-frequency parameters.
            ack_eliciting_threshold: 1,
            max_ack_delay: Duration::from_millis(25),
        }
    }

    /// equivalent to BBREnterStartup <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.1-3>
    fn enter_startup(&mut self) {
        self.state = BbrState::Startup;
        self.pacing_gain = self.startup_pacing_gain;
        self.cwnd_gain = self.default_cwnd_gain;
    }

    /// equivalent to BBRResetFullBW <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.2-4>
    fn reset_full_bw(&mut self) {
        self.full_bw = 0.0;
        self.full_bw_count = 0;
        self.full_bw_now = false;
    }

    /// equivalent to BBRNoteLoss <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-11>
    fn note_loss(&mut self) {
        if !self.loss_in_round {
            self.loss_round_delivered = self.delivered;
        }
        self.save_state_upon_loss();
        self.loss_in_round = true;
        self.loss_events_in_round = self.loss_events_in_round.saturating_add(1);
    }

    /// equivalent to BBRSaveStateUponLoss <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.11.1>
    /// Save state in case a loss episode is later declared spurious
    fn save_state_upon_loss(&mut self) {
        self.undo_state = self.state;
        self.undo_bw_shortterm = self.bw_shortterm;
        self.undo_inflight_shortterm = self.inflight_shortterm;
        self.undo_inflight_longterm = self.inflight_longterm;
    }

    /// equivalent to BBRInflightAtLoss <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-11>
    /// We check at what prefix of packet did losses exceed `loss_thresh`
    fn inflight_at_loss(&mut self, packet_size: u64) -> u64 {
        let Some(rate_sample) = self.rs else {
            return 0;
        };
        let inflight_prev = rate_sample.tx_in_flight.saturating_sub(packet_size) as f64;
        let lost_prev = rate_sample.lost.saturating_sub(packet_size) as f64;
        let lost_prefix = (LOSS_THRESH * inflight_prev - lost_prev) / (1.0 - LOSS_THRESH);
        (inflight_prev + lost_prefix) as u64
    }

    /// equivalent to BBRSaveCwnd <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.4-13>
    fn save_cwnd(&mut self) {
        if !self.loss_in_round && self.state != BbrState::ProbeRtt {
            self.prior_cwnd = self.cwnd;
        } else {
            self.prior_cwnd = max(self.prior_cwnd, self.cwnd);
        }
    }

    /// equivalent to BBRRestoreCwnd <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.4-13>
    fn restore_cwnd(&mut self) {
        self.cwnd = max(self.cwnd, self.prior_cwnd);
    }

    /// equivalent to BBRProbeRTTCwnd <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.5-1>
    fn probe_rtt_cwnd(&mut self) -> u64 {
        let mut probe_rtt_cwnd = self.bdp_multiple(self.bw, self.probe_rtt_cwnd_gain);
        probe_rtt_cwnd = max(probe_rtt_cwnd, self.min_pipe_cwnd);
        probe_rtt_cwnd
    }

    /// equivalent to BBRBoundCwndForProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.5-1>
    fn bound_cwnd_for_probe_rtt(&mut self) {
        if self.state == BbrState::ProbeRtt {
            self.cwnd = min(self.cwnd, self.probe_rtt_cwnd());
        }
    }

    /// equivalent to BBRTargetInflight <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-6>
    fn target_inflight(&self) -> u64 {
        min(self.bdp, self.cwnd)
    }

    /// equivalent to BBRHandleInflightTooHigh <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-1>
    fn handle_inflight_too_high(&mut self, now: Instant) {
        self.bw_probe_samples = false;
        if let Some(rate_sample) = self.rs
            && !rate_sample.is_app_limited
        {
            self.inflight_longterm = max(
                rate_sample.tx_in_flight,
                (self.target_inflight() as f64 * BETA) as u64,
            );
        }

        if self.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
            self.start_probe_bw_down(now);
        }
    }

    /// equivalent to IsInflightTooHigh <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-1>
    fn is_inflight_too_high(&self) -> bool {
        if let Some(rate_sample) = self.rs {
            return rate_sample.lost as f64 > rate_sample.tx_in_flight as f64 * LOSS_THRESH;
        }
        false
    }

    /// equivalent to BBRCheckStartupHighLoss <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#section-5.3.1.3>
    ///
    /// Exits STARTUP on loss when all three draft criteria are met over a single
    /// round trip:
    ///  1. the flow has been losing for at least one full round trip
    ///     (`loss_round_start` && `loss_in_round`),
    ///  2. the loss rate exceeds `LOSS_THRESH` (via `is_inflight_too_high`),
    ///  3. at least `STARTUP_FULL_LOSS_CNT` discontiguous loss events occurred in
    ///     that round trip (`loss_events_in_round`).
    ///
    /// The draft's alternative rule for connections without selective ACKs ("exit
    /// on any loss during fast recovery") does not apply: QUIC ACKs are always
    /// selective, so `C.has_selective_acks` is effectively always true. This is
    /// the same reason `is_inflight_too_high` omits the non-SACK clause.
    fn check_startup_high_loss(&mut self) {
        if self.full_bw_reached {
            return;
        }

        if self.loss_round_start
            && self.loss_events_in_round >= STARTUP_FULL_LOSS_CNT
            && self.is_inflight_too_high()
        {
            let mut new_inflight_hi = self.bdp.max(self.inflight_latest);
            if let Some(rate_sample) = self.rs
                && new_inflight_hi < rate_sample.delivered
            {
                new_inflight_hi = rate_sample.delivered;
            }
            self.inflight_longterm = new_inflight_hi;
            self.full_bw_reached = true;
            self.full_bw_now = true;
        }

        if self.loss_round_start {
            self.loss_events_in_round = 0;
        }
    }

    /// equivalent to BBREnterProbeBW <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6>
    fn enter_probe_bw(&mut self, now: Instant) {
        self.cwnd_gain = self.default_cwnd_gain;
        self.start_probe_bw_down(now);
    }

    /// equivalent to BBRPickProbeWait <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-6>
    fn pick_probe_wait(&mut self) {
        // 0 or 1
        self.rounds_since_bw_probe = self.probe_rng.random_bool(0.5) as u64;
        self.bw_probe_wait = Duration::from_millis(
            MIN_PROBE_WAIT_MS + self.probe_rng.random_range(0..=MAX_ADDED_PROBE_WAIT_MS),
        );
    }

    /// equivalent to BBRHasElapsedInPhase <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn has_elapsed_in_phase(&mut self, interval: Duration, now: Instant) -> bool {
        if let Some(cycle_stamp) = self.cycle_stamp {
            now > cycle_stamp.checked_add(interval).unwrap_or(cycle_stamp)
        } else {
            true
        }
    }

    /// equivalent to BBRExitProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.4>
    fn exit_probe_rtt(&mut self, now: Instant) {
        self.reset_short_term_model();
        if self.full_bw_reached {
            self.start_probe_bw_down(now);
            self.start_probe_bw_cruise();
        } else {
            self.enter_startup();
        }
    }

    /// equivalent to BBRCheckProbeRTTDone <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.3-4>
    fn check_probe_rtt_done(&mut self, now: Instant) {
        if let Some(probe_rtt_done_stamp) = self.probe_rtt_done_stamp
            && now > probe_rtt_done_stamp
        {
            self.probe_rtt_min_stamp = Some(now);
            self.restore_cwnd();
            self.exit_probe_rtt(now);
        }
    }

    /// equivalent to BBRIsTimeToProbeBW <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-6>
    fn maybe_enter_probe_bw_refill(&mut self, now: Instant) -> bool {
        if self.has_elapsed_in_phase(self.bw_probe_wait, now)
            || self.is_reno_coexistence_probe_time()
        {
            self.start_probe_bw_refill();
            return true;
        }
        false
    }

    /// equivalent to BBRIsTimeToGoDown <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-6>
    fn maybe_go_down(&mut self) -> bool {
        if self.is_cwnd_limited && self.cwnd >= self.inflight_longterm {
            self.reset_full_bw();
            if let Some(rate_sample) = self.rs {
                self.full_bw = rate_sample.delivery_rate;
            }
        } else if self.full_bw_now {
            return true;
        }
        false
    }

    /// equivalent to BBRIsRenoCoexistenceProbeTime <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.5.3-6>
    fn is_reno_coexistence_probe_time(&self) -> bool {
        let reno_rounds = self.target_inflight();
        let rounds = min(reno_rounds, MAX_RENO_ROUNDS);
        self.rounds_since_bw_probe >= rounds
    }

    /// equivalent to BBRBDPMultiple <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.2-2>
    fn bdp_multiple(&mut self, bw: f64, gain: f64) -> u64 {
        if self.min_rtt == Duration::from_secs(u64::MAX) {
            return self.initial_cwnd;
        }
        self.bdp = (bw * self.min_rtt.as_secs_f64()).round() as u64;
        (gain * self.bdp as f64) as u64
    }

    /// equivalent to BBRUpdateOffloadBudget for QUIC per
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.8.2>.
    ///
    /// The delayed-ACK term accounts for the QUIC ACK frequency extension:
    /// `min(Ack-Eliciting Threshold, Requested Max Ack Delay * BBR.max_bw)`.
    fn update_offload_budget(&mut self) {
        let base = self.send_quantum;

        // Ack-Eliciting Threshold is a packet count in the ACK_FREQUENCY frame; convert to
        // bytes using the current SMSS. A threshold of 0 requires an immediate ACK per packet,
        // so the delayed-ACK term contributes nothing in that case.
        let threshold_bytes = self.ack_eliciting_threshold.saturating_mul(self.smss);
        let delay_bytes = (self.max_ack_delay.as_secs_f64() * self.max_bw).round() as u64;
        let delayed_ack_term = min(threshold_bytes, delay_bytes);

        self.offload_budget = base.saturating_add(delayed_ack_term);
    }

    /// equivalent to BBRQuantizationBudget <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.2-2>
    fn quantization_budget(&mut self, inflight_cap: u64) -> u64 {
        self.update_offload_budget();
        let mut inflight_cap = max(inflight_cap, self.offload_budget);
        inflight_cap = max(inflight_cap, self.min_pipe_cwnd);
        if self.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
            inflight_cap += 2 * self.smss;
        }
        inflight_cap
    }

    /// equivalent to BBRInflight <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.2-2>
    fn get_inflight(&mut self, gain: f64) -> u64 {
        let inflight_cap = self.bdp_multiple(self.max_bw, gain);
        self.quantization_budget(inflight_cap)
    }

    /// equivalent to BBRUpdateMaxInflight <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.2-2>
    fn update_max_inflight(&mut self) {
        let mut inflight_cap = self.bdp_multiple(self.max_bw, self.cwnd_gain);
        inflight_cap += self.extra_acked;
        self.max_inflight = self.quantization_budget(inflight_cap);
    }

    /// equivalent to BBRResetCongestionSignals <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn reset_congestion_signals(&mut self) {
        self.loss_in_round = false;
        self.bw_latest = 0.0;
        self.inflight_latest = 0;
    }

    /// equivalent to BBRStartRound <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.1-9>
    fn start_round(&mut self) {
        self.next_round_delivered = self.delivered;
        self.is_cwnd_limited = false;
    }

    /// equivalent to BBRUpdateRound <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.1-9>
    fn update_round(&mut self, packet: BbrPacket) {
        if packet.delivered >= self.next_round_delivered {
            self.start_round();
            self.round_count += 1;
            self.rounds_since_bw_probe += 1;
            self.round_start = true;
        } else {
            self.round_start = false;
        }
    }

    /// equivalent to BBRStartProbeBW_DOWN <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-4>
    fn start_probe_bw_down(&mut self, now: Instant) {
        self.reset_congestion_signals();
        self.probe_up_cnt = u64::MAX;
        self.pick_probe_wait();
        self.cycle_stamp = Some(now);
        self.ack_phase = AckPhase::ProbeStopping;
        self.start_round();
        self.pacing_gain = self.probe_bw_down_pacing_gain;
        self.cwnd_gain = self.default_cwnd_gain;
        self.state = BbrState::ProbeBw(ProbeBwSubstate::Down);
    }

    /// equivalent to BBRInflightWithHeadroom <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn inflight_with_headroom(&self) -> u64 {
        if self.inflight_longterm == u64::MAX {
            return u64::MAX;
        }
        let total_headroom = max(self.smss, (HEADROOM * self.inflight_longterm as f64) as u64);
        if let Some(inflight_with_headroom) = self.inflight_longterm.checked_sub(total_headroom) {
            max(inflight_with_headroom, self.min_pipe_cwnd)
        } else {
            self.min_pipe_cwnd
        }
    }

    /// equivalent to BBRSetPacingRateWithGain <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.2-7>
    fn set_pacing_rate_with_gain(&mut self, gain: f64) {
        let rate = gain * self.bw * (100.0 - self.pacing_margin_percent) / 100.0;
        if self.full_bw_reached || rate > self.pacing_rate {
            self.pacing_rate = rate;
        }
    }

    /// equivalent to BBRRaiseInflightLongtermSlope <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn raise_inflight_long_term_slope(&mut self) {
        let growth_this_round = self
            .smss
            .checked_shl(self.bw_probe_up_rounds)
            .unwrap_or(u64::MAX);
        self.bw_probe_up_rounds = min(self.bw_probe_up_rounds + 1, MAX_LONG_TERM_PROBE_UP_ROUNDS);
        self.probe_up_cnt = max(self.cwnd / growth_this_round, 1);
    }

    /// equivalent to BBRProbeInflightLongtermUpward <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn probe_inflight_long_term_upward(&mut self) {
        if !self.is_cwnd_limited || self.cwnd < self.inflight_longterm {
            return;
        }
        if let Some(rate_sample) = self.rs {
            self.bw_probe_up_acks += rate_sample.newly_acked;
        }
        if self.bw_probe_up_acks >= self.probe_up_cnt && self.probe_up_cnt > 0 {
            let delta = self.bw_probe_up_acks / self.probe_up_cnt;
            self.bw_probe_up_acks -= delta * self.probe_up_cnt;
            self.inflight_longterm += delta;
            if self.round_start {
                self.raise_inflight_long_term_slope();
            }
        }
    }

    /// equivalent to BBRAdvanceMaxBwFilter <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.6>
    fn advance_max_bw_filter(&mut self) {
        self.cycle_count = self.cycle_count.saturating_add(1);
    }

    /// equivalent to BBRAdaptLongTermModel <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn adapt_long_term_model(&mut self) {
        if self.ack_phase == AckPhase::ProbeStarting && self.round_start {
            self.ack_phase = AckPhase::ProbeFeedback;
        }
        if self.ack_phase == AckPhase::ProbeStopping
            && self.round_start
            && let BbrState::ProbeBw(_) = self.state
            && let Some(rate_sample) = self.rs
            && !rate_sample.is_app_limited
        {
            self.advance_max_bw_filter();
        }
        if !self.is_inflight_too_high() {
            if self.inflight_longterm == u64::MAX {
                return;
            }
            if let Some(rate_sample) = self.rs
                && rate_sample.tx_in_flight > self.inflight_longterm
            {
                self.inflight_longterm = rate_sample.tx_in_flight;
            }
            if self.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
                self.probe_inflight_long_term_upward();
            }
        }
    }

    /// equivalent to BBRIsTimeToCruise <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    fn maybe_update_budget_and_time_to_cruise(&mut self) -> bool {
        if self.inflight > self.inflight_with_headroom() {
            return false;
        }
        if self.inflight > self.get_inflight(1.0) {
            return false;
        }
        true
    }

    /// equivalent to BBRStartProbeBW_CRUISE <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.4-4>
    fn start_probe_bw_cruise(&mut self) {
        self.state = BbrState::ProbeBw(ProbeBwSubstate::Cruise);
        self.pacing_gain = self.default_pacing_gain;
        self.cwnd_gain = self.default_cwnd_gain;
    }

    /// equivalent to BBRResetShortTermModel <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn reset_short_term_model(&mut self) {
        self.bw_shortterm = f64::INFINITY;
        self.inflight_shortterm = u64::MAX;
    }

    /// equivalent to BBRInitLowerBounds <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn init_lower_bounds(&mut self) {
        if self.bw_shortterm == f64::INFINITY {
            self.bw_shortterm = self.max_bw;
        }
        if self.inflight_shortterm == u64::MAX {
            self.inflight_shortterm = self.cwnd;
        }
    }

    /// equivalent to BBRLossLowerBounds <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn loss_lower_bounds(&mut self) {
        // gives max of both f64
        self.bw_shortterm = [self.bw_latest, BETA * self.bw_shortterm]
            .iter()
            .copied()
            .fold(f64::NAN, f64::max);
        self.inflight_shortterm = max(
            self.inflight_latest,
            (BETA * self.inflight_shortterm as f64) as u64,
        );
    }

    /// equivalent to BBRBoundBWForModel <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn bound_bw_for_model(&mut self) {
        // gives min of both f64
        self.bw = [self.max_bw, self.bw_shortterm]
            .iter()
            .copied()
            .fold(f64::NAN, f64::min);
    }

    /// equivalent to BBRStartProbeBW_REFILL <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-4>
    fn start_probe_bw_refill(&mut self) {
        self.reset_short_term_model();
        self.bw_probe_up_rounds = 0;
        self.bw_probe_up_acks = 0;
        self.ack_phase = AckPhase::Refilling;
        self.start_round();
        self.cwnd_gain = self.default_cwnd_gain;
        self.pacing_gain = self.default_pacing_gain;
        self.state = BbrState::ProbeBw(ProbeBwSubstate::Refill);
    }

    /// equivalent to BBRStartProbeBW_UP <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-4>
    fn start_probe_bw_up(&mut self) {
        self.ack_phase = AckPhase::ProbeStarting;
        self.start_round();
        self.reset_full_bw();
        if let Some(rate_sample) = self.rs {
            self.full_bw = rate_sample.delivery_rate;
        }
        self.state = BbrState::ProbeBw(ProbeBwSubstate::Up);
        self.pacing_gain = self.probe_bw_up_pacing_gain;
        self.cwnd_gain = self.probe_bw_up_cwnd_gain;
        self.raise_inflight_long_term_slope();
    }

    /// equivalent to BBREnterProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.3-4>
    fn enter_probe_rtt(&mut self) {
        self.state = BbrState::ProbeRtt;
        self.pacing_gain = self.default_pacing_gain;
        self.cwnd_gain = self.probe_rtt_cwnd_gain;
    }

    /// equivalent to BBRHandleRestartFromIdle <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.4.1>
    fn handle_restart_from_idle(&mut self, now: Instant) {
        if self.inflight == 0 && self.app_limited != 0 {
            self.idle_restart = true;
            self.extra_acked_interval_start = Some(now);
            match self.state {
                BbrState::ProbeBw(_) => {
                    self.set_pacing_rate_with_gain(1.0);
                }
                BbrState::ProbeRtt => {
                    self.check_probe_rtt_done(now);
                }
                _ => {}
            }
        }
    }

    /// equivalent to BBRUpdateProbeBWCyclePhase <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-6>
    fn update_probe_bw_cycle_phase(&mut self, now: Instant) {
        if !self.full_bw_reached {
            return;
        }
        self.adapt_long_term_model();
        let state = self.state;
        match state {
            BbrState::ProbeBw(ProbeBwSubstate::Down) => {
                if self.maybe_enter_probe_bw_refill(now) {
                    return;
                }
                if self.maybe_update_budget_and_time_to_cruise() {
                    self.start_probe_bw_cruise();
                }
            }
            BbrState::ProbeBw(ProbeBwSubstate::Cruise) if self.maybe_enter_probe_bw_refill(now) => {
            }
            BbrState::ProbeBw(ProbeBwSubstate::Refill) if self.round_start => {
                self.bw_probe_samples = true;
                self.start_probe_bw_up();
            }
            BbrState::ProbeBw(ProbeBwSubstate::Up) if self.maybe_go_down() => {
                self.start_probe_bw_down(now);
            }
            _ => {}
        }
    }

    /// equivalent to BBRUpdateLatestDeliverySignals <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn update_latest_delivery_signals(&mut self) {
        self.loss_round_start = false;
        if let Some(rate_sample) = self.rs {
            self.bw_latest = [self.bw_latest, rate_sample.delivery_rate]
                .iter()
                .copied()
                .fold(f64::NAN, f64::max);
            self.inflight_latest = max(self.inflight_latest, rate_sample.delivered);

            if rate_sample.prior_delivered >= self.loss_round_delivered {
                self.loss_round_delivered = self.delivered;
                self.loss_round_start = true;
            }
        }
    }

    /// equivalent to BBRAdaptLowerBoundsFromCongestion <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn adapt_lower_bounds_from_congestion(&mut self) {
        match self.state {
            BbrState::ProbeBw(ProbeBwSubstate::Refill)
            | BbrState::ProbeBw(ProbeBwSubstate::Up)
            | BbrState::Startup => {}
            _ => {
                if self.loss_in_round {
                    self.init_lower_bounds();
                    self.loss_lower_bounds();
                }
            }
        }
    }

    /// equivalent to BBRUpdateMaxBw <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.5>
    fn update_max_bw(&mut self, p: BbrPacket) {
        self.update_round(p);
        if let Some(rate_sample) = self.rs
            && rate_sample.delivery_rate > 0.0
            && (rate_sample.delivery_rate >= self.max_bw || !rate_sample.is_app_limited)
        {
            self.max_bw_filter
                .update_max(self.cycle_count, rate_sample.delivery_rate.round() as u64);

            self.max_bw = self.max_bw_filter.get_max() as f64;
        }
    }

    /// equivalent to BBRUpdateCongestionSignals <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn update_congestion_signals(&mut self, p: BbrPacket) {
        self.update_max_bw(p);
        if !self.loss_round_start {
            return;
        }
        self.adapt_lower_bounds_from_congestion();
        self.loss_in_round = false;
    }

    /// equivalent to BBRUpdateACKAggregation <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.9>
    fn update_ack_aggregation(&mut self, now: Instant) {
        let interval;
        if let Some(extra_acked_interval_start) = self.extra_acked_interval_start {
            interval = now - extra_acked_interval_start;
        } else {
            interval = Duration::from_secs(0);
        }
        let mut expected_delivered = (self.bw * interval.as_secs_f64()) as u64;
        if self.extra_acked_delivered <= expected_delivered {
            self.extra_acked_delivered = 0;
            self.extra_acked_interval_start = Some(now);
            expected_delivered = 0;
        }
        if let Some(rate_sample) = self.rs {
            self.extra_acked_delivered += rate_sample.newly_acked;
        }

        let mut extra = self
            .extra_acked_delivered
            .saturating_sub(expected_delivered);
        extra = min(extra, self.cwnd);
        if self.full_bw_reached {
            self.extra_acked_filter.update_max(self.round_count, extra);
            self.extra_acked = self.extra_acked_filter.get_max();
        } else {
            self.extra_acked = extra; // In startup, just remember 1 round
        }
    }

    /// equivalent to BBRCheckFullBWReached <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.2-6>
    fn check_full_bw_reached(&mut self) {
        if self.full_bw_now || !self.round_start {
            return;
        }
        if let Some(rate_sample) = self.rs {
            if rate_sample.is_app_limited {
                return;
            }
            if rate_sample.delivery_rate >= self.full_bw * FULL_BW_GROWTH {
                self.reset_full_bw();
                self.full_bw = rate_sample.delivery_rate;
                return;
            }
        }
        self.full_bw_count += 1;
        self.full_bw_now = self.full_bw_count >= MAX_FULL_BW_COUNT;
        if self.full_bw_now {
            self.full_bw_reached = true;
        }
    }

    /// equivalent to BBREnterDrain <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.2>
    fn enter_drain(&mut self) {
        self.state = BbrState::Drain;
        self.pacing_gain = self.drain_pacing_gain;
        self.cwnd_gain = self.default_cwnd_gain;
        self.drain_start_round = self.round_count;
    }

    /// equivalent to BBRCheckStartupDone <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.1.1-6>
    fn check_startup_done(&mut self) {
        self.check_startup_high_loss();
        if self.state == BbrState::Startup && self.full_bw_reached {
            self.enter_drain();
        }
    }

    /// equivalent to BBRCheckDrainDone <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.2-3>
    fn check_drain_done(&mut self, now: Instant) {
        if self.state == BbrState::Drain
            && (self.inflight <= self.get_inflight(1.0)
                || self.round_count > self.drain_start_round + 3)
        {
            self.enter_probe_bw(now);
        }
    }

    /// equivalent to BBRUpdateMinRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.3>
    fn update_min_rtt(&mut self, now: Instant) {
        if let Some(probe_rtt_min_stamp) = self.probe_rtt_min_stamp {
            self.probe_rtt_expired = now
                > probe_rtt_min_stamp
                    .checked_add(self.probe_rtt_interval)
                    .unwrap_or(probe_rtt_min_stamp);
        } else {
            self.probe_rtt_expired = true;
        }
        if let Some(rate_sample) = self.rs
            && rate_sample.rtt >= Duration::from_secs(0)
            && (rate_sample.rtt < self.probe_rtt_min_delay || self.probe_rtt_expired)
        {
            self.probe_rtt_min_delay = rate_sample.rtt;
            self.probe_rtt_min_stamp = Some(now);
        }

        let min_rtt_expired;
        if let Some(min_rtt_stamp) = self.min_rtt_stamp {
            min_rtt_expired = now
                > min_rtt_stamp
                    .checked_add(Duration::from_secs(MIN_RTT_FILTER_LEN))
                    .unwrap_or(min_rtt_stamp);
        } else {
            min_rtt_expired = true;
        }
        if self.probe_rtt_min_delay < self.min_rtt || min_rtt_expired {
            self.min_rtt = self.probe_rtt_min_delay;
            self.min_rtt_stamp = self.probe_rtt_min_stamp;
        }
    }

    /// equivalent to BBRHandleProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.3-4>
    fn handle_probe_rtt(&mut self, now: Instant) {
        if self.probe_rtt_done_stamp.is_none() && self.inflight <= self.probe_rtt_cwnd() {
            self.probe_rtt_done_stamp =
                Some(now.checked_add(self.probe_rtt_duration).unwrap_or(now));
            self.probe_rtt_round_done = false;
            self.start_round();
        } else if self.probe_rtt_done_stamp.is_some() {
            if self.round_start {
                self.probe_rtt_round_done = true;
            }
            if self.probe_rtt_round_done {
                self.check_probe_rtt_done(now);
            }
        }
    }

    /// equivalent to BBRCheckProbeRTT <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.4.3-4>
    fn check_probe_rtt(&mut self, now: Instant) {
        match self.state {
            BbrState::ProbeRtt => {
                self.handle_probe_rtt(now);
            }
            _ => {
                if self.probe_rtt_expired && !self.idle_restart {
                    self.enter_probe_rtt();
                    self.save_cwnd();
                    self.probe_rtt_done_stamp = None;
                    self.ack_phase = AckPhase::ProbeStopping;
                    self.start_round();
                }
            }
        }
        if let Some(rate_sample) = self.rs
            && rate_sample.delivered > 0
        {
            self.idle_restart = false;
        }
    }

    /// equivalent to BBRAdvanceLatestDeliverySignals <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.3-8>
    fn advance_latest_delivery_signals(&mut self) {
        if self.loss_round_start
            && let Some(rate_sample) = self.rs
        {
            self.bw_latest = rate_sample.delivery_rate;
            self.inflight_latest = rate_sample.delivered;
        }
    }

    /// equivalent to BBRUpdateModelAndState <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.2.3>
    fn update_model_and_state(&mut self, p: BbrPacket, now: Instant) {
        self.update_latest_delivery_signals();
        self.update_congestion_signals(p);
        self.update_ack_aggregation(now);
        self.check_full_bw_reached();
        self.check_startup_done();
        self.check_drain_done(now);
        self.update_probe_bw_cycle_phase(now);
        self.update_min_rtt(now);
        self.check_probe_rtt(now);
        self.advance_latest_delivery_signals();
        self.bound_bw_for_model();
    }

    /// equivalent to BBRSetPacingRate <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.2-7>
    fn set_pacing_rate(&mut self) {
        self.set_pacing_rate_with_gain(self.pacing_gain);
    }

    /// equivalent to BBRSetSendQuantum <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.3>
    /// this version is based on a version of bbr2 from quiche
    fn set_send_quantum(&mut self) {
        self.send_quantum = match self.pacing_rate {
            rate if rate < PACING_RATE_1_2MBPS => MAX_DATAGRAM_SIZE,
            rate if rate < PACING_RATE_24MBPS => 2 * MAX_DATAGRAM_SIZE,
            _ => min((self.pacing_rate / 1000.0) as u64, HIGH_PACE_MAX_QUANTUM),
        };
    }

    /// equivalent to BBRBoundCwndForModel <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.7>
    fn bound_cwnd_for_model(&mut self) {
        let mut cap = u64::MAX;
        match self.state {
            BbrState::ProbeRtt => {
                cap = self.inflight_with_headroom();
            }
            BbrState::ProbeBw(ProbeBwSubstate::Cruise) => {
                cap = self.inflight_with_headroom();
            }
            BbrState::ProbeBw(_) => {
                cap = self.inflight_longterm;
            }
            _ => {}
        }
        cap = min(cap, self.inflight_shortterm);
        cap = max(cap, self.min_pipe_cwnd);
        self.cwnd = min(self.cwnd, cap);
    }

    /// equivalent to BBRSetCwnd <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.6.4.6>
    fn set_cwnd(&mut self) {
        self.update_max_inflight();
        if self.full_bw_reached {
            if let Some(rate_sample) = self.rs {
                self.cwnd = min(self.cwnd + rate_sample.newly_acked, self.max_inflight);
            } else {
                self.cwnd = min(self.cwnd, self.max_inflight);
            }
        } else if (self.cwnd < self.max_inflight || self.delivered < self.initial_cwnd)
            && let Some(rate_sample) = self.rs
        {
            self.cwnd += rate_sample.newly_acked;
        }
        self.cwnd = max(self.cwnd, self.min_pipe_cwnd);
        self.bound_cwnd_for_probe_rtt();
        self.bound_cwnd_for_model();
    }

    /// equivalent to BBRUpdateControlParameters <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.2.3>
    fn update_control_parameters(&mut self) {
        self.set_pacing_rate();
        self.set_send_quantum();
        self.set_cwnd();
    }

    /// equivalent to IsNewestPacket <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-4.1.2.3-3>
    fn is_newest_packet(&self, send_time: Instant, end_seq: u64) -> bool {
        if let Some(first_send_time) = self.first_send_time {
            if send_time > first_send_time {
                return true;
            }
            if let Some(rate_sample) = self.rs
                && end_seq > rate_sample.last_end_seq
            {
                return true;
            }
        }
        false
    }

    /// equivalent to BBRHandleLostPacket <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-11>
    fn process_lost_packet(&mut self, lost_bytes: u64, packet_index: usize, now: Instant) {
        let p = self.packets[packet_index];
        self.note_loss();
        if !self.bw_probe_samples {
            self.packets.remove(packet_index);
            return;
        }
        if let Some(mut rate_sample) = self.rs {
            rate_sample.newly_lost += lost_bytes;
            rate_sample.tx_in_flight = p.tx_in_flight;
            rate_sample.lost = self.lost.saturating_sub(p.lost);
            rate_sample.is_app_limited = p.is_app_limited;
            self.rs = Some(rate_sample);
            if self.is_inflight_too_high() {
                rate_sample.tx_in_flight = self.inflight_at_loss(p.size as u64);
                self.rs = Some(rate_sample);
                self.handle_inflight_too_high(now);
            }
        }
        self.packets.remove(packet_index);
    }
}
impl Controller for Bbr3 {
    fn on_packet_sent(&mut self, now: Instant, bytes: u16, pn: u64) {
        if self.inflight == 0 {
            self.first_send_time = Some(now);
            self.delivered_time = Some(now);
        }
        let added_bytes = bytes as u64;
        self.inflight += added_bytes;
        self.packets.push_back(BbrPacket {
            delivered: self.delivered,
            delivered_time: self.delivered_time.unwrap_or(now),
            first_send_time: self.first_send_time.unwrap_or(now),
            send_time: now,
            is_app_limited: self.app_limited != 0,
            tx_in_flight: self.inflight,
            packet_number: pn,
            size: bytes,
            lost: self.lost,
            acknowledged: false,
            stale: false,
            round_count: self.round_count,
        });
        self.handle_restart_from_idle(now);
    }

    fn on_ack(
        &mut self,
        now: Instant,
        sent: Instant,
        bytes: u64,
        pn: u64,
        _app_limited: bool,
        rtt: &RttEstimator,
    ) {
        if let Some(mut rate_sample) = self.rs {
            rate_sample.newly_acked += bytes;
            self.rs = Some(rate_sample);
            self.delivered += bytes;
            self.delivered_time = Some(now);
        }
        let p_index_result = self.packets.binary_search_by_key(&pn, |p| p.packet_number);
        let is_newest_packet = self.is_newest_packet(sent, pn);
        if let Ok(p_index) = p_index_result
            && let Some(p) = self.packets.get_mut(p_index)
        {
            p.acknowledged = true;
            if let Some(mut rate_sample) = self.rs {
                rate_sample.rtt = now - p.send_time;
                if is_newest_packet {
                    self.srtt = rtt.get();
                    rate_sample.prior_delivered = p.delivered;
                    rate_sample.prior_time = p.delivered_time;
                    rate_sample.is_app_limited = p.is_app_limited;
                    rate_sample.tx_in_flight = p.tx_in_flight;
                    rate_sample.lost = self.lost.saturating_sub(p.lost);
                    rate_sample.send_elapsed = p.send_time - p.first_send_time;
                    rate_sample.ack_elapsed = self.delivered_time.unwrap_or(now) - p.delivered_time;
                    rate_sample.last_end_seq = pn;
                    self.first_send_time = Some(p.send_time);
                    rate_sample.last_packet = *p;
                    self.rs = Some(rate_sample);
                    self.update_model_and_state(rate_sample.last_packet, now);
                    self.update_control_parameters();
                }
            } else {
                let rate_sample = BbrRateSample {
                    rtt: rtt.get(),
                    prior_time: p.delivered_time,
                    interval: Duration::ZERO,
                    delivery_rate: 0.0,
                    is_app_limited: p.is_app_limited,
                    delivered: 0,
                    prior_delivered: p.delivered,
                    tx_in_flight: p.tx_in_flight,
                    send_elapsed: p.send_time - p.first_send_time,
                    ack_elapsed: self.delivered_time.unwrap_or(now) - p.delivered_time,
                    newly_acked: bytes,
                    newly_lost: 0,
                    lost: self.lost.saturating_sub(p.lost),
                    last_end_seq: pn,
                    last_packet: *p,
                };
                self.rs = Some(rate_sample);
                self.first_send_time = Some(p.send_time);
                self.srtt = rate_sample.rtt;
                self.update_model_and_state(rate_sample.last_packet, now);
                self.update_control_parameters();
            }
        }
    }

    fn on_end_acks(
        &mut self,
        _now: Instant,
        in_flight: u64,
        app_limited: bool,
        largest_packet_num_acked: Option<u64>,
    ) {
        self.inflight = in_flight;
        if let Some(largest_packet_num) = largest_packet_num_acked {
            if self.app_limited != 0 && largest_packet_num > self.app_limited {
                self.app_limited = 0;
            } else if app_limited {
                self.app_limited = self.app_limited.max(largest_packet_num);
            }
            self.packets.retain(|&p| !p.stale);
            for p in self.packets.iter_mut() {
                if p.acknowledged || self.round_count - p.round_count > ROUND_COUNT_WINDOW {
                    p.stale = true;
                }
            }
            if let Some(mut rate_sample) = self.rs {
                if rate_sample.prior_delivered == 0 {
                    return;
                }
                rate_sample.interval = max(rate_sample.send_elapsed, rate_sample.ack_elapsed);
                rate_sample.delivered = self.delivered.saturating_sub(rate_sample.prior_delivered);
                // ignore this condition on an initially high min rtt as per <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-4.1.2.3-5>
                if rate_sample.interval < self.min_rtt
                    && self.min_rtt != Duration::from_secs(u64::MAX)
                {
                    return;
                }
                if rate_sample.interval != Duration::ZERO {
                    rate_sample.delivery_rate =
                        rate_sample.delivered as f64 / rate_sample.interval.as_secs_f64();
                }
                if rate_sample.delivered >= self.cwnd {
                    self.is_cwnd_limited = true;
                }
                self.rs = Some(rate_sample);
                rate_sample.newly_acked = 0;
                rate_sample.lost = 0;
                rate_sample.newly_lost = 0;
                self.rs = Some(rate_sample);
            }
        }
    }

    fn on_congestion_event(
        &mut self,
        now: Instant,
        _sent: Instant,
        is_persistent_congestion: bool,
        is_ecn: bool,
        lost_bytes: u64,
        largest_lost_pn: u64,
    ) {
        // only process ecn here, regular packet loss is detected per packet in on_packet_lost.
        if is_ecn {
            self.lost += lost_bytes;
            let p_index_result = self
                .packets
                .binary_search_by_key(&largest_lost_pn, |p| p.packet_number);
            if let Ok(p_index) = p_index_result {
                self.process_lost_packet(lost_bytes, p_index, now);
            }
            if is_persistent_congestion {
                self.cwnd = self.min_pipe_cwnd;
            }
        }
    }

    fn on_packet_lost(&mut self, lost_bytes: u16, pn: u64, now: Instant) {
        let lost_bytes_64 = lost_bytes as u64;
        self.lost += lost_bytes_64;
        let p_index_result = self.packets.binary_search_by_key(&pn, |p| p.packet_number);
        if let Ok(p_index) = p_index_result {
            self.process_lost_packet(lost_bytes_64, p_index, now);
        }
    }

    /// equivalent to BBRHandleSpuriousLossDetection: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.11.2>
    fn on_spurious_congestion_event(&mut self) {
        self.loss_in_round = false;
        self.reset_full_bw();
        self.bw_shortterm = [self.bw_shortterm, self.undo_bw_shortterm]
            .iter()
            .copied()
            .fold(f64::NAN, f64::max);
        self.inflight_shortterm = max(self.inflight_shortterm, self.undo_inflight_shortterm);
        self.inflight_longterm = max(self.inflight_longterm, self.undo_inflight_longterm);
        if self.state != BbrState::ProbeRtt && self.state != self.undo_state {
            if self.undo_state == BbrState::Startup {
                self.enter_startup();
            } else if self.undo_state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
                self.start_probe_bw_up();
            }
        }
    }

    fn on_mtu_update(&mut self, new_mtu: u16) {
        self.smss = min(
            max(MIN_MAX_DATAGRAM_SIZE, new_mtu) as u64,
            MAX_DATAGRAM_SIZE,
        );
        self.set_cwnd();
    }

    fn on_ack_frequency_update(
        &mut self,
        ack_eliciting_threshold: u64,
        requested_max_ack_delay: Duration,
    ) {
        self.ack_eliciting_threshold = ack_eliciting_threshold;
        self.max_ack_delay = requested_max_ack_delay;
    }

    fn window(&self) -> u64 {
        self.cwnd
    }

    fn metrics(&self) -> ControllerMetrics {
        ControllerMetrics {
            congestion_window: self.window(),
            ssthresh: None,
            pacing_rate: Some(self.pacing_rate.round() as u64),
            send_quantum: Some(self.send_quantum),
        }
    }

    fn clone_box(&self) -> Box<dyn Controller> {
        Box::new(self.clone())
    }

    fn initial_window(&self) -> u64 {
        self.initial_cwnd
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

/// Configuration for the `Bbr3` congestion controller
///
/// Different pacing_gains can be set to modify the multiplier used to
/// increase the sending rates.
/// Different cwnd_gains can be set to modify the multiplier used to increase
/// the congestion windows.
/// All of these parameters are specific to different states of the algorithm: see `BbrState`
/// `pacing_margin_percent` is used to set a margin when calculating the `pacing_rate` in order
/// to not send at 100% capacity when calculating pacing.
#[derive(Debug, Clone)]
pub struct Bbr3Config {
    initial_window: u64,
    probe_rng_seed: Option<[u8; 16]>,
    startup_pacing_gain: Option<f64>,
    default_pacing_gain: Option<f64>,
    probe_bw_down_pacing_gain: Option<f64>,
    probe_bw_up_pacing_gain: Option<f64>,
    probe_bw_up_cwnd_gain: Option<f64>,
    probe_rtt_cwnd_gain: Option<f64>,
    drain_pacing_gain: Option<f64>,
    pacing_margin_percent: Option<f64>,
    default_cwnd_gain: Option<f64>,
}

impl Bbr3Config {
    /// Default limit on the amount of outstanding data in bytes.
    ///
    /// Recommended value: `min(10 * max_datagram_size, max(2 * max_datagram_size, 14720))`
    pub fn initial_window(&mut self, value: u64) -> &mut Self {
        self.initial_window = value;
        self
    }
}

impl Default for Bbr3Config {
    fn default() -> Self {
        Self {
            initial_window: 14720.clamp(2 * MAX_DATAGRAM_SIZE, 10 * MAX_DATAGRAM_SIZE),
            probe_rng_seed: None,
            startup_pacing_gain: None,
            default_pacing_gain: None,
            probe_bw_down_pacing_gain: None,
            probe_bw_up_pacing_gain: None,
            probe_bw_up_cwnd_gain: None,
            probe_rtt_cwnd_gain: None,
            drain_pacing_gain: None,
            pacing_margin_percent: None,
            default_cwnd_gain: None,
        }
    }
}

impl ControllerFactory for Bbr3Config {
    fn build(self: Arc<Self>, _now: Instant, current_mtu: u16) -> Box<dyn Controller> {
        Box::new(Bbr3::new(self, current_mtu))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_probe_rng() {
        let seed: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let config = Bbr3Config {
            initial_window: 14720.clamp(2 * MAX_DATAGRAM_SIZE, 10 * MAX_DATAGRAM_SIZE),
            probe_rng_seed: Some(seed),
            startup_pacing_gain: None,
            default_pacing_gain: None,
            probe_bw_down_pacing_gain: None,
            probe_bw_up_pacing_gain: None,
            probe_bw_up_cwnd_gain: None,
            probe_rtt_cwnd_gain: None,
            drain_pacing_gain: None,
            pacing_margin_percent: None,
            default_cwnd_gain: None,
        };
        let mut bbr3 = Bbr3::new(Arc::new(config), 2500);
        bbr3.pick_probe_wait();
        assert_eq!(bbr3.rounds_since_bw_probe, 1);
        assert_eq!(bbr3.bw_probe_wait, Duration::from_millis(2652));
        bbr3.pick_probe_wait();
        assert_eq!(bbr3.rounds_since_bw_probe, 1);
        assert_eq!(bbr3.bw_probe_wait, Duration::from_millis(2570));
    }

    /// A.1 — Exiting STARTUP on a bandwidth plateau.
    /// equivalent to: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#name-exiting-startup-on-bandwidt>
    /// Drives a flow through the real `on_packet_sent`/`on_ack`/`on_end_acks`
    /// path against a single-bottleneck link simulator: a constant bandwidth
    /// `BW`, constant propagation `RTT`, and an infinite buffer (no loss).
    /// Packets queue at the bottleneck and are served at `BW`, so once the pipe
    /// fills the delivery-rate samples BBR measures plateau at `BW`. The sender
    /// always has data queued, so it is never application-limited.
    ///
    /// Asserts that, once the measured delivery rate stops growing by >=25% for
    /// 3 consecutive rounds (`full_bw_count` == `MAX_FULL_BW_COUNT`),
    /// `full_bw_now`/`full_bw_reached` are set, the bandwidth estimate
    /// (`max_bw`) sits within 2% of the simulated link bandwidth, and the flow
    /// transitions from STARTUP straight to DRAIN.
    #[test]
    fn startup_exits_to_drain_on_bandwidth_plateau() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// Simulated propagation round-trip time. Kept large (100ms) so the
        /// transient ProbeRTT that BBR enters on the first ack (its
        /// `probe_rtt_min_stamp` starts unset, initializing `min_rtt`) spans
        /// fewer than `MAX_FULL_BW_COUNT` rounds and cannot falsely complete the
        /// plateau there; the flow bounces back to STARTUP and ramps cleanly.
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // captured on the STARTUP -> DRAIN edge (DRAIN is only ever entered from
        // STARTUP, via check_startup_done). BBR dips through a transient ProbeRTT
        // right after the first ack, so we run until DRAIN rather than breaking on
        // the first non-STARTUP state.
        let mut transition: Option<(u64, bool, bool, f64)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let can_send = inflight + MSS <= cwnd;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // The sender always has data; send whenever the window allows and a
            // send is due no later than the next ack, otherwise process an ack.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                // pace the next send at BBR's chosen pacing rate
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, false, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, false, Some(p.pn));
                if bbr.state == BbrState::Drain {
                    transition = Some((
                        bbr.full_bw_count,
                        bbr.full_bw_now,
                        bbr.full_bw_reached,
                        bbr.max_bw,
                    ));
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // The break condition guarantees we landed on the STARTUP -> DRAIN edge.
        let (full_bw_count, full_bw_now, full_bw_reached, max_bw) =
            transition.expect("BBR never left STARTUP");

        // Plateau detected: 3 consecutive rounds with <25% delivery-rate growth.
        assert_eq!(full_bw_count, MAX_FULL_BW_COUNT);
        assert!(full_bw_now, "full_bw_now should be set on plateau");
        assert!(full_bw_reached, "full_bw_reached should be set on plateau");
        // Bandwidth estimate within 2% of the simulated link bandwidth.
        let err = (max_bw - BW).abs() / BW;
        assert!(
            err < 0.02,
            "max_bw {max_bw} not within 2% of simulated {BW} (rel err {err})"
        );
    }

    /// A.2 — Exiting STARTUP on loss when application-limited.
    /// equivalent to: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#name-exiting-startup-on-loss-whe>
    ///
    /// Drives a STARTUP flow whose delivery-rate samples are all
    /// application-limited (the app keeps only `APP_WINDOW` bytes outstanding, well
    /// below cwnd), so `check_full_bw_reached` bails on every round
    /// (`rate_sample.is_app_limited` short-circuit) and the bandwidth-plateau
    /// path can never end STARTUP. Loss is then injected above `LOSS_THRESH`
    /// (2%), with at least `STARTUP_FULL_LOSS_CNT` discontiguous losses per round
    /// trip, so `check_startup_high_loss` observes the high loss rate and ends
    /// STARTUP: `full_bw_now`/`full_bw_reached` become true and the flow
    /// transitions STARTUP -> DRAIN, purely from loss.
    #[test]
    fn startup_exits_to_drain_on_loss_when_app_limited() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;
        /// application window: bytes the app keeps outstanding. Fixed and well
        /// below the STARTUP cwnd so the sender is application-limited (never
        /// cwnd-limited), which blocks the bandwidth-plateau exit and isolates
        /// the loss path. Sized so a single round trip carries at least
        /// `STARTUP_FULL_LOSS_CNT` losses at the `LOSS_PERIOD` rate below.
        const APP_WINDOW: u64 = 200 * MSS;
        /// drop 1 in every `LOSS_PERIOD` packets -> 4% loss, above `LOSS_THRESH`
        /// (2%), spread evenly so each round trip carries loss over its full
        /// sequence range.
        const LOSS_PERIOD: u64 = 25;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
            lost: bool,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // Whether BBRCheckStartupHighLoss ever observed a too-high loss rate
        // (the A.2 signal). Sampled right after each ack is processed.
        let mut observed_high_loss = false;

        // captured on the STARTUP -> DRAIN edge (DRAIN is only ever entered from
        // STARTUP, via check_startup_done). A transient ProbeRTT dip right after
        // the first ack bounces back to STARTUP, so we run until DRAIN.
        let mut transition: Option<(u64, bool, bool)> = None;

        for _ in 0..1_000_000 {
            // Application-limited: only send while the (small) app window has
            // room, independent of cwnd.
            let can_send = inflight + MSS <= APP_WINDOW.min(bbr.window());
            let next_ack = flight.front().map(|p| p.ack_ns);

            if can_send && next_ack.is_none_or(|ack| now_ns <= ack) {
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;
                let lost = pn % LOSS_PERIOD == LOSS_PERIOD - 1;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                    lost,
                });
                // Emulate the connection layer's C.app_limited (the index of the
                // last packet sent while the app had no more data). BBR's folded
                // `on_end_acks` can only ever raise `app_limited` to the largest
                // *acked* pn and clears it as soon as a larger pn is acked, so it
                // cannot keep samples app-limited on its own; set it to the last
                // sent pn, as a genuinely app-limited quinn connection would.
                bbr.app_limited = pn;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                if p.lost {
                    bbr.on_packet_lost(MSS as u16, p.pn, at(now_ns));
                } else {
                    rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                    bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, true, &rtt_est);
                }
                // Sample before on_end_acks clears the rate sample's loss fields.
                observed_high_loss |= bbr.is_inflight_too_high();
                bbr.on_end_acks(at(now_ns), inflight, true, Some(p.pn));
                if bbr.state == BbrState::Drain {
                    transition = Some((bbr.full_bw_count, bbr.full_bw_now, bbr.full_bw_reached));
                    break;
                }
            } else {
                // app window drained and nothing left to ack: advance to next send
                now_ns += btl_service_ns;
            }
        }

        // Landed on the STARTUP -> DRAIN edge.
        let (full_bw_count, full_bw_now, full_bw_reached) =
            transition.expect("BBR never left STARTUP on loss");

        // Loss, not the plateau path, drove the exit: the plateau path is
        // blocked by app-limited samples, so full_bw_count stayed below the
        // 3-round plateau threshold.
        assert!(
            full_bw_count < MAX_FULL_BW_COUNT,
            "expected loss-driven exit, but plateau counter reached {full_bw_count}"
        );
        assert!(
            observed_high_loss,
            "BBRCheckStartupHighLoss never observed a too-high loss rate"
        );
        assert!(
            full_bw_reached,
            "full_bw_reached should be set on high loss"
        );
        assert!(full_bw_now, "full_bw_now should be set on high loss");
    }

    /// A.3 — Exiting DRAIN based on inflight.
    /// equivalent to: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#name-exiting-drain-based-on-infl>
    ///
    /// Drives a flow through STARTUP -> DRAIN on the same infinite-buffer,
    /// single-bottleneck simulator as A.1, then keeps the same send/ack loop
    /// running through DRAIN. Entering DRAIN sets `pacing_gain` to
    /// `DrainPacingGain` (0.5) while `cwnd_gain` stays at the default, so the
    /// window stays wide but pacing sends the flow slower than the link delivers.
    /// The queue built during STARTUP drains and `C.inflight` falls.
    ///
    /// Asserts that on the STARTUP -> DRAIN edge `pacing_gain == DRAIN_PACING_GAIN`
    /// (0.5), and that DRAIN ends via the inflight branch of `check_drain_done`
    /// (`C.inflight <= BBRInflight(1.0)`, i.e. `get_inflight(1.0)`, the estimated
    /// BDP at unit gain) rather than the `drain_start_round + 3` round fallback,
    /// transitioning to PROBE_BW (substate DOWN).
    #[test]
    fn drain_exits_to_probe_bw_on_inflight() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // pacing_gain observed on the STARTUP -> DRAIN edge (0.5), and the round
        // in which DRAIN started, captured once when DRAIN is first entered.
        let mut drain_pacing_gain: Option<f64> = None;
        let mut drain_start_round: u64 = 0;
        // captured on the DRAIN -> PROBE_BW edge: (state, inflight at exit,
        // BBRInflight(1.0) == get_inflight(1.0), round_count).
        let mut probe_bw_transition: Option<(BbrState, u64, u64, u64)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let can_send = inflight + MSS <= cwnd;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // The sender always has data; send whenever the window allows and a
            // send is due no later than the next ack, otherwise process an ack.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                // pace the next send at BBR's chosen pacing rate; in DRAIN this
                // is BW * 0.5, so the flow sends slower than the link delivers.
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, false, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, false, Some(p.pn));

                // Capture the STARTUP -> DRAIN edge: entering DRAIN sets
                // pacing_gain to DrainPacingGain (0.5) and records the round.
                if bbr.state == BbrState::Drain && drain_pacing_gain.is_none() {
                    drain_pacing_gain = Some(bbr.pacing_gain);
                    drain_start_round = bbr.drain_start_round;
                }

                // Capture the DRAIN -> PROBE_BW edge. get_inflight(1.0) is
                // BBRInflight(1.0), the estimated BDP at unit gain that
                // check_drain_done compares C.inflight against.
                if matches!(bbr.state, BbrState::ProbeBw(_)) {
                    let bdp = bbr.get_inflight(1.0);
                    probe_bw_transition = Some((bbr.state, inflight, bdp, bbr.round_count));
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // Entered DRAIN with the drain pacing gain (0.5).
        let drain_pacing_gain = drain_pacing_gain.expect("BBR never entered DRAIN");
        assert_eq!(
            drain_pacing_gain, DRAIN_PACING_GAIN,
            "DRAIN pacing_gain should be DrainPacingGain (0.5)"
        );

        // Landed on the DRAIN -> PROBE_BW edge.
        let (state, inflight_at_exit, bdp, round_count) =
            probe_bw_transition.expect("BBR never left DRAIN");

        // DRAIN enters PROBE_BW at DOWN, but the same ack may advance DOWN ->
        // CRUISE (the inflight condition that ends DRAIN also opens the
        // time-to-cruise gate). Refill can't fire on entry, so DOWN and CRUISE are
        // the only legitimate entry substates.
        assert!(
            matches!(
                state,
                BbrState::ProbeBw(ProbeBwSubstate::Down | ProbeBwSubstate::Cruise)
            ),
            "DRAIN should transition to PROBE_BW (DOWN or same-ack CRUISE), got {state:?}"
        );

        // The inflight branch of check_drain_done drove the exit: C.inflight fell
        // to/below BBRInflight(1.0), and it happened within the 3-round window so
        // the `drain_start_round + 3` fallback did not fire.
        assert!(
            inflight_at_exit <= bdp,
            "expected inflight-driven DRAIN exit: inflight {inflight_at_exit} > BBRInflight(1.0) {bdp}"
        );
        assert!(
            round_count <= drain_start_round + 3,
            "expected inflight-driven exit, but the round fallback fired \
             (round_count {round_count} > drain_start_round {drain_start_round} + 3)"
        );
    }

    /// A.4 — Exiting DRAIN based on time.
    /// equivalent to: <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-06.html#name-exiting-drain-based-on-time>
    ///
    /// Same simulator as A.1/A.3, driven through STARTUP -> DRAIN. On the DRAIN
    /// edge the link is cut, simulating a STARTUP bandwidth over-estimate: DRAIN
    /// keeps pacing off the stale (too-high) `max_bw`, so the queue never drains
    /// and `C.inflight` stays above `BBRInflight(1.0)` (`get_inflight(1.0)`) for
    /// several rounds. The inflight branch of `check_drain_done` never fires, so
    /// the time fallback exits DRAIN once `round_count > drain_start_round + 3`,
    /// even though `C.inflight` has not reached the target BDP.
    #[test]
    fn drain_exits_to_probe_bw_on_time() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// STARTUP bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// propagation round-trip time (100ms), matching A.1/A.3
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;
        /// Fraction of the STARTUP bandwidth surviving into DRAIN. `max_bw` holds
        /// its STARTUP peak through DRAIN, so DRAIN paces at 0.5 * BW. The draft's
        /// 10% cut is too small here: at 0.9 * BW the link still outruns that
        /// pacing and the queue drains (inflight-branch exit). The surviving link
        /// must be below 0.5 * BW for the queue to persist, so use 0.4.
        const DRAIN_BW_FACTOR: f64 = 0.4;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // bottleneck serialization time per MSS; cut on the DRAIN edge
        let mut btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        let mut drain_start_round: Option<u64> = None;
        // per-round (round_count, inflight, bdp) while in DRAIN
        let mut drain_round_samples: Vec<(u64, u64, u64)> = Vec::new();
        let mut last_sampled_round: Option<u64> = None;
        // DRAIN -> PROBE_BW edge: (state, inflight, bdp, round)
        let mut probe_bw_transition: Option<(BbrState, u64, u64, u64)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let can_send = inflight + MSS <= cwnd;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // The sender always has data; send whenever the window allows and a
            // send is due no later than the next ack, otherwise process an ack.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at the current rate
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, false, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, false, Some(p.pn));

                // STARTUP -> DRAIN edge: cut the link (over-estimate), record round
                if bbr.state == BbrState::Drain && drain_start_round.is_none() {
                    drain_start_round = Some(bbr.drain_start_round);
                    btl_service_ns = (MSS as f64 / (BW * DRAIN_BW_FACTOR) * 1e9).round() as u64;
                }

                // sample inflight vs BBRInflight(1.0) once per DRAIN round
                if bbr.state == BbrState::Drain && last_sampled_round != Some(bbr.round_count) {
                    let bdp = bbr.get_inflight(1.0);
                    drain_round_samples.push((bbr.round_count, inflight, bdp));
                    last_sampled_round = Some(bbr.round_count);
                }

                if matches!(bbr.state, BbrState::ProbeBw(_)) {
                    let bdp = bbr.get_inflight(1.0);
                    probe_bw_transition = Some((bbr.state, inflight, bdp, bbr.round_count));
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        let drain_start_round = drain_start_round.expect("BBR never entered DRAIN");
        let (state, inflight_at_exit, bdp_at_exit, round_count) =
            probe_bw_transition.expect("BBR never left DRAIN");

        // DRAIN exits to PROBE_BW.
        assert!(
            matches!(
                state,
                BbrState::ProbeBw(ProbeBwSubstate::Down | ProbeBwSubstate::Cruise)
            ),
            "DRAIN should transition to PROBE_BW, got {state:?}"
        );

        // Time fallback drove the exit: after 3 full DRAIN rounds...
        assert!(
            round_count > drain_start_round + 3,
            "expected time-driven DRAIN exit at round_count > drain_start_round + 3, \
             got round_count {round_count}, drain_start_round {drain_start_round}"
        );

        // ...with C.inflight still above target (inflight branch never fired).
        assert!(
            inflight_at_exit > bdp_at_exit,
            "expected time-driven exit with inflight still above target: \
             inflight {inflight_at_exit} <= BBRInflight(1.0) {bdp_at_exit}"
        );

        // inflight stayed above target every round in DRAIN
        assert!(
            drain_round_samples.iter().all(|&(_, ifl, bdp)| ifl > bdp),
            "C.inflight dropped to/below BBRInflight(1.0) during DRAIN: {drain_round_samples:?}"
        );
        assert!(
            drain_round_samples.len() >= 3,
            "expected several round trips observed in DRAIN, got {}",
            drain_round_samples.len()
        );
    }

    /// A.5 — Exiting PROBE_UP on a bandwidth plateau.
    /// equivalent to BBRIsTimeToGoDown:
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-6>
    ///
    /// Same infinite-buffer, single-bottleneck simulator as A.1/A.3 (constant
    /// bandwidth `BW`, constant propagation `RTT`, no loss), driven through
    /// STARTUP -> DRAIN -> PROBE_BW and kept running until PROBE_BW cycles into
    /// its PROBE_UP phase. In PROBE_UP `pacing_gain` is `ProbeBwUpPacingGain`
    /// (1.25), so the sender pushes above the link rate and a standing queue
    /// forms at the bottleneck. `inflight_longterm`/`cwnd` grow to fully utilize
    /// that queue with no loss, but the measured delivery rate is pinned at `BW`
    /// and plateaus.
    ///
    /// Asserts that once the delivery rate grows by <25% for 3 consecutive rounds
    /// (`check_full_bw_reached` drives `full_bw_count` to `MAX_FULL_BW_COUNT` and
    /// sets `full_bw_now`), `BBRIsTimeToGoDown()` (`maybe_go_down`) fires and the
    /// flow transitions PROBE_UP -> PROBE_DOWN. On the deciding round-start ack
    /// `is_cwnd_limited` has just been cleared by `start_round`, so the "keep
    /// probing" branch of `maybe_go_down` is skipped and the plateau drives the
    /// exit.
    #[test]
    fn probe_bw_exits_probe_up_to_probe_down_on_bandwidth_plateau() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1/A.3
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // Whether the flow has reached the PROBE_UP phase of PROBE_BW; the go-down
        // edge we care about is PROBE_UP -> PROBE_DOWN, distinct from the initial
        // DRAIN -> PROBE_BW(DOWN) entry.
        let mut reached_probe_up = false;
        // Captured on the PROBE_UP -> PROBE_DOWN edge: (state, full_bw_count,
        // full_bw_now). start_probe_bw_down leaves full_bw_count/full_bw_now
        // untouched, so they still read the plateau values right after the edge.
        let mut go_down_transition: Option<(BbrState, u64, bool)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let can_send = inflight + MSS <= cwnd;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // The sender always has data; send whenever the window allows and a
            // send is due no later than the next ack, otherwise process an ack.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                // pace the next send at BBR's chosen pacing rate; in PROBE_UP this
                // is BW * 1.25, so the flow overshoots and builds a queue.
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, false, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, false, Some(p.pn));

                if bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
                    reached_probe_up = true;
                }

                // Capture the PROBE_UP -> PROBE_DOWN edge (only meaningful once
                // PROBE_UP has actually been entered).
                if reached_probe_up && bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Down) {
                    go_down_transition = Some((bbr.state, bbr.full_bw_count, bbr.full_bw_now));
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // Landed on the PROBE_UP -> PROBE_DOWN edge.
        assert!(reached_probe_up, "BBR never reached the PROBE_UP phase");
        let (state, full_bw_count, full_bw_now) =
            go_down_transition.expect("BBR never left PROBE_UP");

        // Plateau drove the exit: 3 consecutive rounds with <25% delivery-rate
        // growth set full_bw_now, and BBRIsTimeToGoDown() moved to PROBE_DOWN.
        assert_eq!(
            full_bw_count, MAX_FULL_BW_COUNT,
            "full_bw_count should reach MAX_FULL_BW_COUNT on the plateau"
        );
        assert!(full_bw_now, "full_bw_now should be set on the plateau");
        assert_eq!(
            state,
            BbrState::ProbeBw(ProbeBwSubstate::Down),
            "PROBE_UP should transition to PROBE_DOWN on the plateau"
        );
    }

    /// A.6 — Exiting PROBE_UP on loss when application-limited.
    /// equivalent to BBRHandleInflightTooHigh:
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.5.10.2-1>
    ///
    /// NOTE: the loss-driven PROBE_UP exit runs through `handle_inflight_too_high`
    /// (BBRHandleInflightTooHigh), reached per-lost-packet from
    /// `process_lost_packet`, NOT through `maybe_go_down` (BBRIsTimeToGoDown).
    /// BBRIsTimeToGoDown only inspects the cwnd-limited/plateau signals
    /// (`full_bw_now`) and never the loss rate, so high loss cannot trigger it;
    /// the plateau path (A.5) is what BBRIsTimeToGoDown covers. This test drives
    /// the actual code path that ends PROBE_UP on excess loss.
    ///
    /// Same single-bottleneck simulator as A.1/A.3/A.5, run in two phases:
    ///  1. Not application-limited, no loss, full-cwnd (identical to A.5) until
    ///     the flow cycles STARTUP -> DRAIN -> PROBE_BW -> PROBE_UP.
    ///  2. Once PROBE_UP is entered, the app is throttled to a small fixed window
    ///     (`APP_WINDOW`, well below cwnd) so every fresh sample is
    ///     application-limited, and 1-in-`LOSS_PERIOD` packets are dropped -> a
    ///     per-round loss rate (4%) above `BBR.LossThresh` (2%).
    ///
    /// In PROBE_UP `bw_probe_samples` is true, so each lost packet is fed through
    /// `process_lost_packet`; `is_inflight_too_high()` sees the loss exceed
    /// `LOSS_THRESH * tx_in_flight` and calls `handle_inflight_too_high`. Because
    /// the deciding sample is application-limited, the `!is_app_limited` guard in
    /// `handle_inflight_too_high` skips the `inflight_longterm` reduction (an
    /// app-limited loss sample is not trusted to lower the long-term model), yet
    /// the `state == PROBE_UP` branch still runs `start_probe_bw_down`
    /// unconditionally.
    ///
    /// Asserts that, purely from loss, the flow transitions PROBE_UP ->
    /// PROBE_DOWN with the deciding sample flagged application-limited, that the
    /// plateau path did NOT drive it (`full_bw_now` stays false — blocked by the
    /// app-limited short-circuit in `check_full_bw_reached`), and that
    /// `inflight_longterm` is updated appropriately for an app-limited sample,
    /// i.e. left unchanged across the transition rather than lowered.
    #[test]
    fn probe_bw_exits_probe_up_to_probe_down_on_loss_when_app_limited() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1/A.3/A.5
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;
        /// application window used once PROBE_UP is reached: bytes the app keeps
        /// outstanding. Fixed and well below the PROBE_UP cwnd (~2*BDP, ~1000
        /// packets here) so the sender is application-limited (never
        /// cwnd-limited), which keeps every sample app-limited and isolates the
        /// loss path. Matches A.2's window.
        const APP_WINDOW: u64 = 200 * MSS;
        /// drop 1 in every `LOSS_PERIOD` packets -> 4% loss, above `LOSS_THRESH`
        /// (2%), spread evenly so each round trip carries loss over its full
        /// sequence range.
        const LOSS_PERIOD: u64 = 25;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
            lost: bool,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // Phase 2 begins once PROBE_UP is reached: from then the app is limited
        // to APP_WINDOW and packets are dropped at the LOSS_PERIOD rate.
        let mut app_limited_phase = false;
        let mut reached_probe_up = false;
        // Captured on the loss-driven PROBE_UP -> PROBE_DOWN edge:
        // (inflight_longterm before/after the deciding loss, whether the deciding
        // sample was app-limited, full_bw_now at the edge).
        let mut go_down: Option<(u64, u64, bool, bool)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let window_cap = if app_limited_phase {
                APP_WINDOW.min(cwnd)
            } else {
                cwnd
            };
            let can_send = inflight + MSS <= window_cap;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // Send whenever the window allows and a paced send is due no later
            // than the next ack; otherwise process an ack. In the app-limited
            // phase the small window is the binding limit, not cwnd.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;
                // Only drop packets once app-limited (phase 2); phase 1 is loss
                // free so the flow reaches PROBE_UP exactly as in A.5.
                let lost = app_limited_phase && pn % LOSS_PERIOD == LOSS_PERIOD - 1;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                    lost,
                });

                if app_limited_phase {
                    // Emulate the connection layer's C.app_limited (the index of
                    // the last packet sent while the app had no more data) so the
                    // next packet is stamped app-limited at send time. Same shape
                    // as A.2: on_end_acks cannot keep samples app-limited on its
                    // own, so drive it here.
                    bbr.app_limited = pn;
                }

                // pace the next send at BBR's chosen pacing rate
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                if p.lost {
                    // Capture the loss-driven PROBE_UP -> PROBE_DOWN edge. The
                    // transition happens inside on_packet_lost (via
                    // handle_inflight_too_high), never on an ack, so any Up->Down
                    // move seen here is attributable to this loss.
                    let before_ilt = bbr.inflight_longterm;
                    let was_up = bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Up);
                    bbr.on_packet_lost(MSS as u16, p.pn, at(now_ns));
                    if was_up && bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Down) {
                        let app_lim = bbr.rs.is_some_and(|rs| rs.is_app_limited);
                        go_down =
                            Some((before_ilt, bbr.inflight_longterm, app_lim, bbr.full_bw_now));
                        break;
                    }
                } else {
                    rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                    bbr.on_ack(
                        at(now_ns),
                        at(p.send_ns),
                        MSS,
                        p.pn,
                        app_limited_phase,
                        &rtt_est,
                    );
                    bbr.on_end_acks(at(now_ns), inflight, app_limited_phase, Some(p.pn));

                    // Flip to the application-limited, lossy phase the moment
                    // PROBE_BW is entered, so that by the time the cycle reaches
                    // PROBE_UP the pipe has already drained to APP_WINDOW and
                    // every in-flight sample is app-limited (the plateau path
                    // cannot fire on stale non-app-limited samples).
                    if !app_limited_phase && matches!(bbr.state, BbrState::ProbeBw(_)) {
                        app_limited_phase = true;
                    }
                    if bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
                        reached_probe_up = true;
                    }
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // Landed on the loss-driven PROBE_UP -> PROBE_DOWN edge.
        assert!(reached_probe_up, "BBR never reached the PROBE_UP phase");
        let (before_ilt, after_ilt, app_lim, full_bw_now) =
            go_down.expect("BBR never left PROBE_UP on loss");

        // The deciding loss sample was application-limited.
        assert!(
            app_lim,
            "deciding loss sample should be application-limited"
        );
        // Loss, not the plateau path, drove the exit: check_full_bw_reached bails
        // on app-limited samples, so full_bw_now (BBRIsTimeToGoDown's plateau
        // signal) never got set.
        assert!(
            !full_bw_now,
            "expected loss-driven exit, but the plateau signal full_bw_now was set"
        );
        // Updated appropriately for an app-limited sample: handle_inflight_too_high
        // skips the reduction (the !is_app_limited guard), so inflight_longterm is
        // left unchanged across the transition rather than lowered toward
        // max(tx_in_flight, target_inflight * BETA). A non-app-limited loss would
        // instead set it here.
        assert_eq!(
            before_ilt, after_ilt,
            "inflight_longterm should be unchanged on an app-limited loss exit"
        );
    }

    /// A.7 — Never exiting STARTUP when application-limited with no loss.
    ///
    /// The negative counterpart to A.1 (plateau exit) and A.2 (loss exit): with
    /// neither signal present, STARTUP must persist. STARTUP leaves for DRAIN only
    /// via `check_startup_done`, which requires `full_bw_reached`
    /// (`self.state == Startup && self.full_bw_reached` -> `enter_drain`), plus the
    /// high-loss escape in `check_startup_high_loss`. When every round is
    /// application-limited, `check_full_bw_reached` bails on the `is_app_limited`
    /// guard, so `full_bw_now`/`full_bw_reached` are never set; with zero loss the
    /// high-loss escape never fires either. Both STARTUP -> DRAIN triggers are
    /// therefore closed.
    ///
    /// The one state change that still occurs is the scheduled min-RTT refresh:
    /// with a constant RTT the min-RTT filter expires every `probe_rtt_interval`
    /// (5s) and `check_probe_rtt` moves STARTUP -> PROBE_RTT. This is orthogonal to
    /// the app-limited/loss exits A.7 concerns — and because `full_bw_reached` is
    /// still false, `exit_probe_rtt` routes back to STARTUP (`enter_startup`)
    /// rather than on to PROBE_BW. So the flow oscillates STARTUP <-> PROBE_RTT and
    /// never advances past STARTUP, i.e. it stays in STARTUP indefinitely.
    ///
    /// Same infinite-buffer, single-bottleneck simulator as A.1/A.2, but the app
    /// is limited to a small fixed window (`APP_WINDOW`, well below cwnd) from the
    /// very first packet so every sample is application-limited, and no packet is
    /// ever dropped.
    ///
    /// Runs long enough (`ROUNDS_TO_OBSERVE`, several `probe_rtt_interval`s) to
    /// cover multiple PROBE_RTT interludes, and asserts that: the flow only ever
    /// occupies STARTUP or PROBE_RTT (never DRAIN/PROBE_BW), at least one
    /// PROBE_RTT interlude was exercised and returned to STARTUP, every observed
    /// sample was application-limited, `full_bw_reached`/`full_bw_now` were never
    /// set, and `full_bw_count` never reached `MAX_FULL_BW_COUNT`.
    #[test]
    fn startup_never_exits_when_app_limited_without_loss() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1/A.2
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;
        /// bytes the app keeps outstanding, from the first packet on. Fixed and
        /// well below cwnd (initial cwnd is ~109*MSS, and the app-limited delivery
        /// rate keeps cwnd = cwnd_gain*bdp ~= 2.77*APP_WINDOW thereafter) so the
        /// sender is application-limited, never cwnd-limited. Comfortably above
        /// `min_pipe_cwnd` (4*MSS).
        const APP_WINDOW: u64 = 20 * MSS;
        /// rounds to observe before declaring "indefinitely". Each round is ~1 RTT
        /// (100ms), so this spans ~16s — several `probe_rtt_interval`s (5s) — and
        /// covers multiple STARTUP <-> PROBE_RTT oscillations.
        const ROUNDS_TO_OBSERVE: u64 = 160;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // Signals gathered over the run; every assertion is checked after the loop.
        // The set of states ever visited (must stay within {Startup, ProbeRtt}).
        let mut saw_probe_rtt = false;
        // A PROBE_RTT interlude was seen and the flow subsequently returned to
        // STARTUP — proof exit_probe_rtt routed back to STARTUP, not on to
        // PROBE_BW.
        let mut returned_to_startup = false;
        // Set true the moment any forbidden (past-STARTUP) state is entered.
        let mut advanced_past_startup: Option<BbrState> = None;
        // Whether every ack we processed carried an application-limited sample.
        let mut all_samples_app_limited = true;
        let mut samples_seen: u64 = 0;
        // Highest full_bw_count / whether full_bw_now/full_bw_reached ever set.
        let mut max_full_bw_count: u64 = 0;
        let mut full_bw_now_ever = false;
        let mut full_bw_reached_ever = false;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            // The app never wants more than APP_WINDOW outstanding.
            let window_cap = APP_WINDOW.min(cwnd);
            let can_send = inflight + MSS <= window_cap;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // Send whenever the small app window allows and a paced send is due no
            // later than the next ack; otherwise process an ack. The app window is
            // always the binding limit, not cwnd.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW (infinite buffer, no
                // loss)
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                // Emulate the connection layer's C.app_limited (index of the last
                // packet sent while the app had no more data) so the next packet is
                // stamped app-limited at send time. Same shape as A.2/A.6.
                bbr.app_limited = pn;

                // pace the next send at BBR's chosen pacing rate
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, true, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, true, Some(p.pn));

                // Record the sample's app-limited flag, but only for STARTUP
                // rounds: PROBE_RTT deliberately clamps cwnd to min_pipe_cwnd
                // (below APP_WINDOW), so its samples are cwnd-limited by design and
                // are not part of the app-limited premise.
                if let Some(rs) = bbr.rs
                    && bbr.state == BbrState::Startup
                {
                    samples_seen += 1;
                    all_samples_app_limited &= rs.is_app_limited;
                }
                max_full_bw_count = max_full_bw_count.max(bbr.full_bw_count);
                full_bw_now_ever |= bbr.full_bw_now;
                full_bw_reached_ever |= bbr.full_bw_reached;

                match bbr.state {
                    BbrState::Startup => {
                        // Returning to STARTUP after a PROBE_RTT interlude confirms
                        // exit_probe_rtt routed back here (full_bw_reached false).
                        if saw_probe_rtt {
                            returned_to_startup = true;
                        }
                    }
                    BbrState::ProbeRtt => {
                        saw_probe_rtt = true;
                    }
                    // Any of these means STARTUP was actually left for the next
                    // phase — the failure A.7 guards against.
                    other => {
                        advanced_past_startup.get_or_insert(other);
                    }
                }

                if advanced_past_startup.is_some() || bbr.round_count >= ROUNDS_TO_OBSERVE {
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // Never advanced past STARTUP: only STARTUP and the scheduled PROBE_RTT
        // min-RTT refresh were ever entered.
        assert!(
            advanced_past_startup.is_none(),
            "BBR left STARTUP for {:?} while application-limited with no loss",
            advanced_past_startup,
        );
        // The run was long enough to actually exercise the oscillation.
        assert!(
            bbr.round_count >= ROUNDS_TO_OBSERVE,
            "simulation ended early ({} rounds) before observing enough rounds",
            bbr.round_count,
        );
        // The min-RTT refresh fired and returned to STARTUP (not on to PROBE_BW),
        // proving STARTUP is genuinely re-entered rather than merely never left
        // because time stood still.
        assert!(saw_probe_rtt, "expected a scheduled PROBE_RTT interlude");
        assert!(
            returned_to_startup,
            "PROBE_RTT should route back to STARTUP while full_bw_reached is false"
        );
        assert_eq!(
            bbr.state,
            BbrState::Startup,
            "BBR should still be in STARTUP at the end of the run"
        );
        // The premise held: every sample really was application-limited.
        assert!(samples_seen > 0, "no samples were observed");
        assert!(
            all_samples_app_limited,
            "every sample should be application-limited"
        );
        // The plateau path never armed: check_full_bw_reached short-circuits on
        // app-limited samples, so full_bw_reached/full_bw_now stayed false and
        // full_bw_count never reached MAX_FULL_BW_COUNT.
        assert!(
            !full_bw_reached_ever,
            "full_bw_reached must never be set on application-limited samples"
        );
        assert!(
            !full_bw_now_ever,
            "full_bw_now must never be set on application-limited samples"
        );
        assert!(
            max_full_bw_count < MAX_FULL_BW_COUNT,
            "full_bw_count must never reach MAX_FULL_BW_COUNT on application-limited samples (was {max_full_bw_count})"
        );
    }

    /// A.8 — Exiting PROBE_DOWN on inflight.
    /// equivalent to BBRIsTimeToCruise:
    /// <https://www.ietf.org/archive/id/draft-ietf-ccwg-bbr-05.html#section-5.3.3.6-8>
    ///
    /// Same infinite-buffer, single-bottleneck simulator as A.5 (constant
    /// bandwidth `BW`, constant propagation `RTT`, no loss, sender always has
    /// data), driven STARTUP -> DRAIN -> PROBE_BW and kept running until PROBE_BW
    /// has cycled through PROBE_UP and back into a PROBE_DOWN phase. PROBE_UP paces
    /// at `ProbeBwUpPacingGain` (1.25) and builds a standing queue, so on the
    /// PROBE_UP -> PROBE_DOWN edge `C.inflight` sits well above both cruise
    /// thresholds — there is a genuine queue to drain (distinct from the very
    /// first DRAIN -> PROBE_DOWN entry, where DRAIN has already emptied the pipe).
    ///
    /// In PROBE_DOWN `pacing_gain` is `ProbeDownPacingGain` (0.90), so the sender
    /// paces below the link rate and the standing queue drains at ~0.1*`BW`. Each
    /// ack runs `update_probe_bw_cycle_phase`, whose PROBE_DOWN arm first checks
    /// `maybe_enter_probe_bw_refill` (still false: `bw_probe_wait` is 2-3s and
    /// `rounds_since_bw_probe` was reset at down entry, so neither the elapsed-time
    /// nor the Reno-coexistence trigger fires within the short drain) and then
    /// `maybe_update_budget_and_time_to_cruise` (`BBRIsTimeToCruise`). The latter
    /// returns true only once `C.inflight` has fallen to <= both
    /// `BBRInflightWithHeadroom()` and `BBRInflight(1.0)`, at which point
    /// `start_probe_bw_cruise` moves PROBE_DOWN -> PROBE_CRUISE.
    ///
    /// `update_probe_bw_cycle_phase` reads `self.inflight`, which the previous
    /// `on_end_acks` set from the simulator's `inflight` one tick earlier, so the
    /// deciding value lags the loop's `inflight` by a single MSS — the same lag
    /// A.3's `check_drain_done` relies on. Because the queue only shrinks, the
    /// post-transition `C.inflight` (slightly smaller still) is likewise <= both
    /// thresholds, so the thresholds recomputed right after the edge witness the
    /// same condition that fired it (`start_probe_bw_cruise` touches neither
    /// `max_bw`, `min_rtt`, `inflight_longterm`, nor `C.inflight`).
    ///
    /// Asserts that: the flow entered PROBE_DOWN via PROBE_UP with
    /// `pacing_gain == ProbeDownPacingGain` (0.90) and `C.inflight` above at least
    /// one cruise threshold (a real queue to drain); the flow then transitioned to
    /// PROBE_CRUISE with `pacing_gain` back at `DefaultPacingGain`; and at that
    /// edge `C.inflight` was <= both `BBRInflightWithHeadroom()` and
    /// `BBRInflight(1.0)`.
    #[test]
    fn probe_bw_exits_probe_down_to_probe_cruise_on_inflight() {
        /// packet size in bytes
        const MSS: u64 = 1200;
        /// simulated bottleneck bandwidth: 100 Mbit/s in bytes/sec
        const BW: f64 = 12_500_000.0;
        /// simulated propagation round-trip time (100ms), matching A.1/A.3/A.5
        const RTT_NS: u64 = 100_000_000;
        const FWD_NS: u64 = RTT_NS / 2;
        const RET_NS: u64 = RTT_NS / 2;

        // bottleneck serialization time for one MSS-sized packet
        let btl_service_ns: u64 = (MSS as f64 / BW * 1e9).round() as u64;

        // Drive the production default configuration.
        let mut bbr = Bbr3::new(Arc::new(Bbr3Config::default()), MSS as u16);
        assert_eq!(bbr.state, BbrState::Startup);

        let base = Instant::now();
        let at = |off_ns: u64| base + Duration::from_nanos(off_ns);
        let mut rtt_est = RttEstimator::new(Duration::from_nanos(RTT_NS));

        struct InFlight {
            pn: u64,
            send_ns: u64,
            ack_ns: u64,
        }
        let mut flight: VecDeque<InFlight> = VecDeque::new();

        let mut now_ns: u64 = 0;
        let mut next_send_ns: u64 = 0;
        // time at which the bottleneck finishes serving everything queued so far
        let mut btl_free_ns: u64 = 0;
        let mut inflight: u64 = 0;
        let mut pn: u64 = 0;

        // Whether the flow has reached the PROBE_UP phase; the PROBE_DOWN we care
        // about is the one PROBE_UP cycles back into (it carries the standing queue
        // PROBE_UP built), not the initial DRAIN -> PROBE_DOWN entry.
        let mut reached_probe_up = false;
        // Captured on the PROBE_UP -> PROBE_DOWN edge: (pacing_gain, C.inflight,
        // BBRInflightWithHeadroom(), BBRInflight(1.0)) at entry, before any drain.
        let mut down_entry: Option<(f64, u64, u64, u64)> = None;
        // Captured on the PROBE_DOWN -> PROBE_CRUISE edge: (pacing_gain,
        // C.inflight, BBRInflightWithHeadroom(), BBRInflight(1.0)).
        let mut cruise_edge: Option<(f64, u64, u64, u64)> = None;

        for _ in 0..1_000_000 {
            let cwnd = bbr.window();
            let can_send = inflight + MSS <= cwnd;
            let next_ack = flight.front().map(|p| p.ack_ns);

            // The sender always has data; send whenever the window allows and a
            // send is due no later than the next ack, otherwise process an ack.
            let do_send = can_send && next_ack.is_none_or(|ack| next_send_ns <= ack);

            if do_send {
                now_ns = now_ns.max(next_send_ns);
                let send_ns = now_ns;
                // enqueue at the FIFO bottleneck, served at BW
                let arrival = send_ns + FWD_NS;
                let service_start = arrival.max(btl_free_ns);
                let finish = service_start + btl_service_ns;
                btl_free_ns = finish;
                let ack_ns = finish + RET_NS;

                bbr.on_packet_sent(at(send_ns), MSS as u16, pn);
                inflight += MSS;
                flight.push_back(InFlight {
                    pn,
                    send_ns,
                    ack_ns,
                });

                // pace the next send at BBR's chosen pacing rate; in PROBE_DOWN
                // this is BW * 0.90, so the flow undershoots and the standing queue
                // built during PROBE_UP drains.
                let pacing = bbr.pacing_rate.max(1.0);
                next_send_ns = send_ns + (MSS as f64 / pacing * 1e9).round() as u64;
                pn += 1;
            } else if let Some(p) = flight.pop_front() {
                now_ns = now_ns.max(p.ack_ns);
                inflight -= MSS;
                rtt_est.update(Duration::ZERO, Duration::from_nanos(now_ns - p.send_ns));
                bbr.on_ack(at(now_ns), at(p.send_ns), MSS, p.pn, false, &rtt_est);
                bbr.on_end_acks(at(now_ns), inflight, false, Some(p.pn));

                if bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Up) {
                    reached_probe_up = true;
                }

                // Capture the PROBE_UP -> PROBE_DOWN entry (only meaningful once
                // PROBE_UP has actually been entered, and only the first time).
                if reached_probe_up
                    && down_entry.is_none()
                    && bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Down)
                {
                    down_entry = Some((
                        bbr.pacing_gain,
                        bbr.inflight,
                        bbr.inflight_with_headroom(),
                        bbr.get_inflight(1.0),
                    ));
                }

                // Capture the PROBE_DOWN -> PROBE_CRUISE edge and stop. Reachable
                // only after the down entry has been recorded.
                if down_entry.is_some() && bbr.state == BbrState::ProbeBw(ProbeBwSubstate::Cruise) {
                    cruise_edge = Some((
                        bbr.pacing_gain,
                        bbr.inflight,
                        bbr.inflight_with_headroom(),
                        bbr.get_inflight(1.0),
                    ));
                    break;
                }
            } else {
                panic!("simulation stalled: window full but nothing in flight");
            }
        }

        // Entered PROBE_DOWN via PROBE_UP, pacing at ProbeDownPacingGain (0.90),
        // with a genuine queue still to drain.
        assert!(reached_probe_up, "BBR never reached the PROBE_UP phase");
        let (down_gain, down_inflight, down_headroom, down_inflight_1) =
            down_entry.expect("BBR never entered PROBE_DOWN after PROBE_UP");
        assert_eq!(
            down_gain, bbr.probe_bw_down_pacing_gain,
            "PROBE_DOWN pacing_gain should be ProbeDownPacingGain"
        );
        assert_eq!(
            down_gain, PROBE_BW_DOWN_PACING_GAIN,
            "ProbeDownPacingGain should be 0.90"
        );
        // A standing queue was present at entry: C.inflight exceeded at least one
        // cruise threshold, so cruise could not fire immediately and a real drain
        // had to happen.
        assert!(
            down_inflight > down_headroom || down_inflight > down_inflight_1,
            "expected a standing queue at PROBE_DOWN entry (inflight {down_inflight} vs \
             headroom {down_headroom}, inflight(1.0) {down_inflight_1})"
        );

        // Drained into PROBE_CRUISE.
        let (cruise_gain, cruise_inflight, cruise_headroom, cruise_inflight_1) =
            cruise_edge.expect("PROBE_DOWN never transitioned to PROBE_CRUISE");
        assert_eq!(
            bbr.state,
            BbrState::ProbeBw(ProbeBwSubstate::Cruise),
            "flow should have transitioned to PROBE_CRUISE"
        );
        // Cruise resets pacing_gain to DefaultPacingGain.
        assert_eq!(
            cruise_gain, bbr.default_pacing_gain,
            "PROBE_CRUISE pacing_gain should be DefaultPacingGain"
        );
        // BBRIsTimeToCruise held: C.inflight fell to <= both thresholds. The queue
        // only shrinks, so the value recomputed just after the edge still <= both,
        // matching the (one-tick-larger) value that actually fired the transition.
        assert!(
            cruise_inflight <= cruise_headroom,
            "at PROBE_CRUISE, inflight ({cruise_inflight}) should be <= \
             BBRInflightWithHeadroom() ({cruise_headroom})"
        );
        assert!(
            cruise_inflight <= cruise_inflight_1,
            "at PROBE_CRUISE, inflight ({cruise_inflight}) should be <= \
             BBRInflight(1.0) ({cruise_inflight_1})"
        );
    }
}
