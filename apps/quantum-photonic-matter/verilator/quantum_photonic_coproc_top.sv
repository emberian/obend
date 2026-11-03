module quantum_photonic_coproc_top (
  input  logic        clk,
  input  logic        rst,
  input  logic [63:0] in_batch_vectors,
  input  logic [63:0] in_syndrome_rounds,
  input  logic [63:0] in_krawtchouk_batch_size,
  input  logic [63:0] in_pst_step_index,
  input  logic [63:0] in_t_num,
  input  logic [63:0] in_t_den,
  input  logic [63:0] in_pin_w0,
  input  logic [63:0] in_pin_w1,
  input  logic [63:0] in_pin_w2,
  input  logic [63:0] in_pin_w3,
  input  logic [63:0] in_pin_shell_w01,
  input  logic [63:0] in_pin_shell_w12,
  input  logic [63:0] in_pin_shell_w23,
  input  logic [63:0] in_target_v0,
  input  logic [63:0] in_target_v1,
  input  logic [63:0] in_target_v2,
  input  logic [63:0] in_target_v3,
  input  logic [63:0] in_tetron_psi0_re,
  input  logic [63:0] in_tetron_psi0_im,
  input  logic [63:0] in_tetron_psi1_re,
  input  logic [63:0] in_tetron_psi1_im,
  input  logic [63:0] in_tetron_psi2_re,
  input  logic [63:0] in_tetron_psi2_im,
  input  logic [63:0] in_tetron_psi3_re,
  input  logic [63:0] in_tetron_psi3_im,
  input  logic [63:0] in_braid_enable,
  output logic [63:0] out_wl_compressed_shells,
  output logic [63:0] out_faddeev_crosstalk_det,
  output logic [63:0] out_cmt_krawtchouk_len0_nm,
  output logic [63:0] out_cmt_krawtchouk_len1_nm,
  output logic [63:0] out_cmt_krawtchouk_len2_nm,
  output logic [63:0] out_quotient_reverse_adjoint_ops,
  output logic [63:0] out_coproc_cycle_budget,
  output logic [63:0] out_krawtchouk_adjoint_macs,
  output logic [63:0] out_pst_transfer_fidelity_ppm,
  output logic [63:0] out_dpr_quotient_usable,
  output logic [63:0] out_dpr_fallback_full,
  output logic [63:0] out_active_hypergraph_wires,
  output logic [63:0] out_active_q3_modes,
  output logic [63:0] out_q3_pst_shell3_imag_scaled,
  output logic [63:0] out_q3_pst_antipodal_enclosed,
  output logic [63:0] out_precomp_u0,
  output logic [63:0] out_precomp_u1,
  output logic [63:0] out_precomp_u2,
  output logic [63:0] out_precomp_u3,
  output logic [63:0] out_channel_y0,
  output logic [63:0] out_channel_y1,
  output logic [63:0] out_channel_y2,
  output logic [63:0] out_channel_y3,
  output logic [63:0] out_crosstalk_exact_match,
  output logic [63:0] out_artin_braid_verified,
  output logic [63:0] out_braid_nonabelian_witness,
  output logic [63:0] out_input_even_parity,
  output logic [63:0] out_input_odd_parity,
  output logic [63:0] out_cool_jump_psi0_re,
  output logic [63:0] out_cool_jump_psi0_im,
  output logic [63:0] out_cool_jump_psi1_re,
  output logic [63:0] out_cool_jump_psi1_im,
  output logic [63:0] out_cool_jump_psi2_re,
  output logic [63:0] out_cool_jump_psi2_im,
  output logic [63:0] out_cool_jump_psi3_re,
  output logic [63:0] out_cool_jump_psi3_im,
  output logic [63:0] out_cooled_in_even_codespace,
  output logic [63:0] out_stabilized_syndrome_epochs,
  output logic [63:0] out_dpr_fallback_events
);
  logic [63:0] w_0; // quotient_reverse_adjoint_ops
  logic [63:0] w_1; // coproc_cycle_budget
  logic [63:0] w_2; // krawtchouk_adjoint_macs
  logic [63:0] w_3; // pst_transfer_fidelity_ppm
  logic [63:0] w_4; // catgrad_w01_eq
  logic [63:0] w_5; // catgrad_w23_eq
  logic [63:0] w_6; // catgrad_sym_ok
  logic [63:0] w_7; // shell_w01_ok
  logic [63:0] w_8; // shell_w12_ok
  logic [63:0] w_9; // shell_w23_ok
  logic [63:0] w_10; // shell_sym_ok
  logic [63:0] w_11; // dpr_quotient_usable
  logic [63:0] w_12; // dpr_fallback_full
  logic [63:0] w_13; // active_hypergraph_wires
  logic [63:0] w_14; // active_q3_modes
  logic [63:0] w_15; // q3_walk_step3_shell3
  logic [63:0] w_16; // t_num_sq
  logic [63:0] w_17; // t_num_cu
  logic [63:0] w_18; // taylor_scale
  logic [63:0] w_19; // q3_pst_shell3_imag_scaled
  logic [63:0] w_20; // q3_pst_antipodal_enclosed
  logic [63:0] w_21; // precomp_u0
  logic [63:0] w_22; // precomp_u1
  logic [63:0] w_23; // precomp_u2
  logic [63:0] w_24; // precomp_u3
  logic [63:0] w_25; // channel_y0
  logic [63:0] w_26; // channel_y1
  logic [63:0] w_27; // channel_y2
  logic [63:0] w_28; // channel_y3
  logic [63:0] w_29; // ct_eq0
  logic [63:0] w_30; // ct_eq1
  logic [63:0] w_31; // ct_eq2
  logic [63:0] w_32; // ct_eq3
  logic [63:0] w_33; // crosstalk_exact_match
  logic [63:0] w_34; // lhs1_z0_re
  logic [63:0] w_35; // lhs1_z0_im
  logic [63:0] w_36; // lhs1_z1_re
  logic [63:0] w_37; // lhs1_z1_im
  logic [63:0] w_38; // lhs1_z2_re
  logic [63:0] w_39; // lhs1_z2_im
  logic [63:0] w_40; // lhs1_z3_re
  logic [63:0] w_41; // lhs1_z3_im
  logic [63:0] w_42; // lhs2_z0_re
  logic [63:0] w_43; // lhs2_z0_im
  logic [63:0] w_44; // lhs2_z1_re
  logic [63:0] w_45; // lhs2_z1_im
  logic [63:0] w_46; // lhs2_z2_re
  logic [63:0] w_47; // lhs2_z2_im
  logic [63:0] w_48; // lhs2_z3_re
  logic [63:0] w_49; // lhs2_z3_im
  logic [63:0] w_50; // lhs3_z0_re
  logic [63:0] w_51; // lhs3_z0_im
  logic [63:0] w_52; // lhs3_z1_re
  logic [63:0] w_53; // lhs3_z1_im
  logic [63:0] w_54; // lhs3_z2_re
  logic [63:0] w_55; // lhs3_z2_im
  logic [63:0] w_56; // lhs3_z3_re
  logic [63:0] w_57; // lhs3_z3_im
  logic [63:0] w_58; // rhs1_z0_re
  logic [63:0] w_59; // rhs1_z0_im
  logic [63:0] w_60; // rhs1_z1_re
  logic [63:0] w_61; // rhs1_z1_im
  logic [63:0] w_62; // rhs1_z2_re
  logic [63:0] w_63; // rhs1_z2_im
  logic [63:0] w_64; // rhs1_z3_re
  logic [63:0] w_65; // rhs1_z3_im
  logic [63:0] w_66; // rhs2_z0_re
  logic [63:0] w_67; // rhs2_z0_im
  logic [63:0] w_68; // rhs2_z1_re
  logic [63:0] w_69; // rhs2_z1_im
  logic [63:0] w_70; // rhs2_z2_re
  logic [63:0] w_71; // rhs2_z2_im
  logic [63:0] w_72; // rhs2_z3_re
  logic [63:0] w_73; // rhs2_z3_im
  logic [63:0] w_74; // rhs3_z0_re
  logic [63:0] w_75; // rhs3_z0_im
  logic [63:0] w_76; // rhs3_z1_re
  logic [63:0] w_77; // rhs3_z1_im
  logic [63:0] w_78; // rhs3_z2_re
  logic [63:0] w_79; // rhs3_z2_im
  logic [63:0] w_80; // rhs3_z3_re
  logic [63:0] w_81; // rhs3_z3_im
  logic [63:0] w_82; // artin3_e0r
  logic [63:0] w_83; // artin3_e0i
  logic [63:0] w_84; // artin3_e1r
  logic [63:0] w_85; // artin3_e1i
  logic [63:0] w_86; // artin3_e2r
  logic [63:0] w_87; // artin3_e2i
  logic [63:0] w_88; // artin3_e3r
  logic [63:0] w_89; // artin3_e3i
  logic [63:0] w_90; // artin3_e01
  logic [63:0] w_91; // artin3_e23
  logic [63:0] w_92; // artin3_all
  logic [63:0] w_93; // comm2_e0r
  logic [63:0] w_94; // comm2_e0i
  logic [63:0] w_95; // comm2_e1r
  logic [63:0] w_96; // comm2_e1i
  logic [63:0] w_97; // comm2_e2r
  logic [63:0] w_98; // comm2_e2i
  logic [63:0] w_99; // comm2_e3r
  logic [63:0] w_100; // comm2_e3i
  logic [63:0] w_101; // comm2_e01
  logic [63:0] w_102; // comm2_e23
  logic [63:0] w_103; // comm2_all
  logic [63:0] w_104; // braid_nonabelian_witness
  logic [63:0] w_105; // z2_zero
  logic [63:0] w_106; // z3_zero
  logic [63:0] w_107; // z0_zero
  logic [63:0] w_108; // z1_zero
  logic [63:0] w_109; // input_even_parity
  logic [63:0] w_110; // input_odd_parity
  logic [63:0] w_111; // cool_z0_re
  logic [63:0] w_112; // cool_z0_im
  logic [63:0] w_113; // cool_z1_re
  logic [63:0] w_114; // cool_z1_im
  logic [63:0] w_115; // cool_z2_re
  logic [63:0] w_116; // cool_z2_im
  logic [63:0] w_117; // cool_z3_re
  logic [63:0] w_118; // cool_z3_im
  logic [63:0] w_119; // cooled_in_even_codespace
  logic [63:0] w_120; // syndrome_epoch_step_en
  logic [63:0] reg_stabilized_syndrome_epochs;
  logic [63:0] reg_dpr_fallback_events;
  always_comb begin
    w_0 = ((in_batch_vectors * 64'd4) + 64'd8769);
    w_1 = (((in_syndrome_rounds * 64'd16) + 64'd4) + 64'd32);
    w_2 = ((in_krawtchouk_batch_size * 64'd4) + 64'd3142);
    w_3 = (((in_pst_step_index * 64'd250) + 64'd4) + 64'd1000);
    w_4 = (in_pin_w0 == in_pin_w1 ? 64'd1 : 64'd0);
    w_5 = (in_pin_w2 == in_pin_w3 ? 64'd1 : 64'd0);
    w_6 = (w_4 & w_5);
    w_7 = (in_pin_shell_w01 == 64'd3 ? 64'd1 : 64'd0);
    w_8 = (in_pin_shell_w12 == 64'd4 ? 64'd1 : 64'd0);
    w_9 = (in_pin_shell_w23 == 64'd3 ? 64'd1 : 64'd0);
    w_10 = ((w_7 & w_8) & w_9);
    w_11 = (w_6 & w_10);
    w_12 = (w_11 == 64'd0 ? 64'd1 : 64'd0);
    w_13 = ((w_11 != 64'd0) ? 64'd12 : 64'd24);
    w_14 = ((w_11 != 64'd0) ? 64'd4 : 64'd8);
    w_15 = (in_pin_shell_w23 * 64'd2);
    w_16 = (in_t_num * in_t_num);
    w_17 = (w_16 * in_t_num);
    w_18 = ((64'd4 * in_t_den) * w_15);
    w_19 = (w_18 * w_17);
    w_20 = (((in_t_num == 64'd157 ? 64'd1 : 64'd0) & (in_t_den == 64'd100 ? 64'd1 : 64'd0)) & w_11);
    w_21 = (((64'd918 * in_target_v0) + (64'd18446744073709551442 * in_target_v1)) + ((64'd18446744073709551553 * in_target_v2) + (64'd30 * in_target_v3)));
    w_22 = (((64'd18446744073709551442 * in_target_v0) + (64'd950 * in_target_v1)) + ((64'd18446744073709551456 * in_target_v2) + (64'd18446744073709551553 * in_target_v3)));
    w_23 = (((64'd18446744073709551553 * in_target_v0) + (64'd18446744073709551456 * in_target_v1)) + ((64'd950 * in_target_v2) + (64'd18446744073709551442 * in_target_v3)));
    w_24 = (((64'd30 * in_target_v0) + (64'd18446744073709551553 * in_target_v1)) + ((64'd18446744073709551442 * in_target_v2) + (64'd918 * in_target_v3)));
    w_25 = (((64'd10 * w_21) + (64'd2 * w_22)) + w_23);
    w_26 = (((64'd2 * w_21) + (64'd10 * w_22)) + ((64'd2 * w_23) + w_24));
    w_27 = ((w_21 + (64'd2 * w_22)) + ((64'd10 * w_23) + (64'd2 * w_24)));
    w_28 = ((w_22 + (64'd2 * w_23)) + (64'd10 * w_24));
    w_29 = (w_25 == (64'd8769 * in_target_v0) ? 64'd1 : 64'd0);
    w_30 = (w_26 == (64'd8769 * in_target_v1) ? 64'd1 : 64'd0);
    w_31 = (w_27 == (64'd8769 * in_target_v2) ? 64'd1 : 64'd0);
    w_32 = (w_28 == (64'd8769 * in_target_v3) ? 64'd1 : 64'd0);
    w_33 = ((w_29 & w_30) & (w_31 & w_32));
    w_34 = (in_tetron_psi0_re - in_tetron_psi1_im);
    w_35 = (in_tetron_psi0_im + in_tetron_psi1_re);
    w_36 = (in_tetron_psi1_re - in_tetron_psi0_im);
    w_37 = (in_tetron_psi1_im + in_tetron_psi0_re);
    w_38 = (in_tetron_psi2_re + in_tetron_psi3_im);
    w_39 = (in_tetron_psi2_im - in_tetron_psi3_re);
    w_40 = (in_tetron_psi3_re + in_tetron_psi2_im);
    w_41 = (in_tetron_psi3_im - in_tetron_psi2_re);
    w_42 = (w_34 - w_35);
    w_43 = (w_34 + w_35);
    w_44 = (w_36 + w_37);
    w_45 = (w_37 - w_36);
    w_46 = (w_38 - w_39);
    w_47 = (w_38 + w_39);
    w_48 = (w_40 + w_41);
    w_49 = (w_41 - w_40);
    w_50 = (w_42 - w_45);
    w_51 = (w_43 + w_44);
    w_52 = (w_44 - w_43);
    w_53 = (w_45 + w_42);
    w_54 = (w_46 + w_49);
    w_55 = (w_47 - w_48);
    w_56 = (w_48 + w_47);
    w_57 = (w_49 - w_46);
    w_58 = (in_tetron_psi0_re - in_tetron_psi0_im);
    w_59 = (in_tetron_psi0_re + in_tetron_psi0_im);
    w_60 = (in_tetron_psi1_re + in_tetron_psi1_im);
    w_61 = (in_tetron_psi1_im - in_tetron_psi1_re);
    w_62 = (in_tetron_psi2_re - in_tetron_psi2_im);
    w_63 = (in_tetron_psi2_re + in_tetron_psi2_im);
    w_64 = (in_tetron_psi3_re + in_tetron_psi3_im);
    w_65 = (in_tetron_psi3_im - in_tetron_psi3_re);
    w_66 = (w_58 - w_61);
    w_67 = (w_59 + w_60);
    w_68 = (w_60 - w_59);
    w_69 = (w_61 + w_58);
    w_70 = (w_62 + w_65);
    w_71 = (w_63 - w_64);
    w_72 = (w_64 + w_63);
    w_73 = (w_65 - w_62);
    w_74 = (w_66 - w_67);
    w_75 = (w_66 + w_67);
    w_76 = (w_68 + w_69);
    w_77 = (w_69 - w_68);
    w_78 = (w_70 - w_71);
    w_79 = (w_70 + w_71);
    w_80 = (w_72 + w_73);
    w_81 = (w_73 - w_72);
    w_82 = (w_50 == w_74 ? 64'd1 : 64'd0);
    w_83 = (w_51 == w_75 ? 64'd1 : 64'd0);
    w_84 = (w_52 == w_76 ? 64'd1 : 64'd0);
    w_85 = (w_53 == w_77 ? 64'd1 : 64'd0);
    w_86 = (w_54 == w_78 ? 64'd1 : 64'd0);
    w_87 = (w_55 == w_79 ? 64'd1 : 64'd0);
    w_88 = (w_56 == w_80 ? 64'd1 : 64'd0);
    w_89 = (w_57 == w_81 ? 64'd1 : 64'd0);
    w_90 = ((w_82 & w_83) & (w_84 & w_85));
    w_91 = ((w_86 & w_87) & (w_88 & w_89));
    w_92 = (w_90 & w_91);
    w_93 = (w_42 == w_66 ? 64'd1 : 64'd0);
    w_94 = (w_43 == w_67 ? 64'd1 : 64'd0);
    w_95 = (w_44 == w_68 ? 64'd1 : 64'd0);
    w_96 = (w_45 == w_69 ? 64'd1 : 64'd0);
    w_97 = (w_46 == w_70 ? 64'd1 : 64'd0);
    w_98 = (w_47 == w_71 ? 64'd1 : 64'd0);
    w_99 = (w_48 == w_72 ? 64'd1 : 64'd0);
    w_100 = (w_49 == w_73 ? 64'd1 : 64'd0);
    w_101 = ((w_93 & w_94) & (w_95 & w_96));
    w_102 = ((w_97 & w_98) & (w_99 & w_100));
    w_103 = (w_101 & w_102);
    w_104 = (w_103 == 64'd0 ? 64'd1 : 64'd0);
    w_105 = ((in_tetron_psi2_re == 64'd0 ? 64'd1 : 64'd0) & (in_tetron_psi2_im == 64'd0 ? 64'd1 : 64'd0));
    w_106 = ((in_tetron_psi3_re == 64'd0 ? 64'd1 : 64'd0) & (in_tetron_psi3_im == 64'd0 ? 64'd1 : 64'd0));
    w_107 = ((in_tetron_psi0_re == 64'd0 ? 64'd1 : 64'd0) & (in_tetron_psi0_im == 64'd0 ? 64'd1 : 64'd0));
    w_108 = ((in_tetron_psi1_re == 64'd0 ? 64'd1 : 64'd0) & (in_tetron_psi1_im == 64'd0 ? 64'd1 : 64'd0));
    w_109 = (w_105 & w_106);
    w_110 = (w_107 & w_108);
    w_111 = in_tetron_psi2_re;
    w_112 = in_tetron_psi2_im;
    w_113 = in_tetron_psi3_re;
    w_114 = in_tetron_psi3_im;
    w_115 = 64'd0;
    w_116 = 64'd0;
    w_117 = 64'd0;
    w_118 = 64'd0;
    w_119 = (((w_115 == 64'd0 ? 64'd1 : 64'd0) & (w_116 == 64'd0 ? 64'd1 : 64'd0)) & ((w_117 == 64'd0 ? 64'd1 : 64'd0) & (w_118 == 64'd0 ? 64'd1 : 64'd0)));
    w_120 = (((in_braid_enable != 64'd0) ? 64'd1 : 64'd0) & (w_92 & w_119));
    out_wl_compressed_shells = 64'd4;
    out_faddeev_crosstalk_det = 64'd8769;
    out_cmt_krawtchouk_len0_nm = 64'd1571;
    out_cmt_krawtchouk_len1_nm = 64'd2721;
    out_cmt_krawtchouk_len2_nm = 64'd3142;
    out_quotient_reverse_adjoint_ops = w_0;
    out_coproc_cycle_budget = w_1;
    out_krawtchouk_adjoint_macs = w_2;
    out_pst_transfer_fidelity_ppm = w_3;
    out_dpr_quotient_usable = w_11;
    out_dpr_fallback_full = w_12;
    out_active_hypergraph_wires = w_13;
    out_active_q3_modes = w_14;
    out_q3_pst_shell3_imag_scaled = w_19;
    out_q3_pst_antipodal_enclosed = w_20;
    out_precomp_u0 = w_21;
    out_precomp_u1 = w_22;
    out_precomp_u2 = w_23;
    out_precomp_u3 = w_24;
    out_channel_y0 = w_25;
    out_channel_y1 = w_26;
    out_channel_y2 = w_27;
    out_channel_y3 = w_28;
    out_crosstalk_exact_match = w_33;
    out_artin_braid_verified = w_92;
    out_braid_nonabelian_witness = w_104;
    out_input_even_parity = w_109;
    out_input_odd_parity = w_110;
    out_cool_jump_psi0_re = w_111;
    out_cool_jump_psi0_im = w_112;
    out_cool_jump_psi1_re = w_113;
    out_cool_jump_psi1_im = w_114;
    out_cool_jump_psi2_re = w_115;
    out_cool_jump_psi2_im = w_116;
    out_cool_jump_psi3_re = w_117;
    out_cool_jump_psi3_im = w_118;
    out_cooled_in_even_codespace = w_119;
    out_stabilized_syndrome_epochs = reg_stabilized_syndrome_epochs;
    out_dpr_fallback_events = reg_dpr_fallback_events;
  end
  // Synchronous-reset control registers
  always_ff @(posedge clk) begin
    if (rst) begin
      reg_stabilized_syndrome_epochs <= 64'd0;
      reg_dpr_fallback_events <= 64'd0;
    end else begin
      reg_stabilized_syndrome_epochs <= ((w_120 != 64'd0) ? (reg_stabilized_syndrome_epochs + 64'd1) : reg_stabilized_syndrome_epochs);
      reg_dpr_fallback_events <= ((w_12 != 64'd0) ? (reg_dpr_fallback_events + 64'd1) : reg_dpr_fallback_events);
    end
  end
endmodule
