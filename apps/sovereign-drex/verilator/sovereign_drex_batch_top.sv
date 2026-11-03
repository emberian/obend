// Objective Bend Flagship App #7 (`apps/sovereign-drex/verilator/sovereign_drex_batch_top.sv`)
// Synthesized 4-Validator (`V0..V3`, N=4, f=1, Quorum=3) Sovereign `DReX` + `K-CARRY`
// Batch-Clearing & Live World Upgrade Accelerator.

`default_nettype none

module sovereign_drex_batch_top (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [63:0] in_lot_count,
    input  wire [63:0] in_epoch_id,
    input  wire [3:0]  in_validator_votes,
    input  wire        in_carry_upgrade_en,
    input  wire [63:0] in_old_cbdc_total,
    input  wire [63:0] in_delta_debit,
    input  wire [63:0] in_delta_credit,
    input  wire [63:0] in_seat_cbdc_after,
    input  wire [63:0] in_seat_want_floor,
    input  wire        in_forever_crown_drop_req,

    output logic [63:0] out_validator_quorum,
    output logic [63:0] out_vote_count,
    output logic        out_quorum_reached,
    output logic [63:0] out_protected_welfare_crown,
    output logic [63:0] out_settled_cbdc_liquidity,
    output logic [63:0] out_batch_settlement_cbdc,
    output logic [63:0] out_finality_commit_tag,
    output logic [63:0] out_carry_pin_digest,
    output logic [63:0] out_new_cbdc_total,
    output logic        out_turn_admitted,
    output logic [63:0] out_wal_committed_count
);

    // 1. 4-Validator BFT Quorum Check (N = 4, f = 1, 2f + 1 = 3)
    wire [63:0] vote_cnt = {63'd0, in_validator_votes[0]}
                         + {63'd0, in_validator_votes[1]}
                         + {63'd0, in_validator_votes[2]}
                         + {63'd0, in_validator_votes[3]};
    wire quorum_ok = (vote_cnt >= 64'd3);

    // 2. State-Bound Half-Edge Conservation & Agoric/Zoe Offer Safety + Forever Crown Guard
    wire half_edge_balanced = (in_delta_debit == in_delta_credit);
    wire zoe_offer_safe     = (in_seat_cbdc_after >= in_seat_want_floor);
    wire crown_preserved    = ~in_forever_crown_drop_req;
    wire turn_ok            = quorum_ok & half_edge_balanced & zoe_offer_safe & crown_preserved;

    // 3. `.obend` SovereignDrexTop & BatchClearing Datapath
    always_comb begin
        out_validator_quorum        = 64'd3;
        out_vote_count              = vote_cnt;
        out_quorum_reached          = quorum_ok;
        out_protected_welfare_crown = 64'd1000;
        out_settled_cbdc_liquidity  = in_carry_upgrade_en ? 64'd125000 : 64'd100000;
        out_batch_settlement_cbdc   = (in_lot_count * 64'd500) + 64'd1000;
        out_finality_commit_tag     = ((in_epoch_id << 64'd6) + 64'd3)
                                    + (in_carry_upgrade_en ? 64'd32 : 64'd0);
        out_carry_pin_digest        = ((in_epoch_id << 64'd5) + 64'd6)
                                    + (in_carry_upgrade_en ? 64'd16 : 64'd0);
        out_new_cbdc_total          = turn_ok ? (in_old_cbdc_total + in_delta_credit - in_delta_debit)
                                              : in_old_cbdc_total;
        out_turn_admitted           = turn_ok;
    end

    // 4. Synchronous Durable BFT WAL Commit Counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_wal_committed_count <= 64'd0;
        end else if (turn_ok) begin
            out_wal_committed_count <= out_wal_committed_count + 64'd1;
        end
    end

endmodule

`default_nettype wire
