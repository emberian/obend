// Continuous-Time 4th-Order Runge-Kutta (RK4, dt = 100 ns) Physics Plant
// for App #2: 20 kHz FOC current loop + SiC FCML controller, co-simulated with foc_drive_top.sv
//
// What this plant is (2026-11-04):
//   1. The LC Drives 4-pole-pair IPM stator in the dq frame (Ld = 150 uH, Lq = 380 uH, Rs = 12 mOhm,
//      psi_PM = 0.18 Wb): the two coupled RL equations below. These are the equations the Lean chain in
//      lean/Obend/Hardware/CurrentLoop.lean discretizes (per axis, with the cross-coupling and back-EMF
//      as the feed-forward `vff`); the same R, L, Ts appear there as free parameters.
//   2. Mechanics, OPT-IN (`enable_mechanics`): J d(omega_m)/dt = T_e - B omega_m - T_load. Off by default so
//      the existing testbench keeps its constant omega_e = 1000 rad/s; the FPGA lane turns it on and
//      re-runs. With it off there is no speed loop and the back-EMF is constant.
//   3. A scalar first-order *phenomenological* model of flying-capacitor unbalance,
//      d(V_unbal)/dt = -5 V_unbal - 800 cap_bal_cmd + ripple. It is NOT a flying-capacitor model
//      (that would be dV_c/dt = i_phase (d_k - d_{k+1}) / C per capacitor, with the sign of the phase
//      current); it responds linearly to the controller's command by construction. Do not read the
//      testbench's "balancing converges" as evidence about an FCML.
//   4. A one-node winding thermal ODE (Rth = 0.045 K/W, Cth = 120 J/K, tau = 5.4 s). In a 50 ms run it
//      moves ~0.4 K; the 155 C trip in the testbench is injected by assignment, so that test exercises
//      the comparator and the write-once latch, not the thermal physics.
// What it is not: there is no inverter between vd/vq and the winding (the commands are applied as
// average voltages; `fcml_duty_permille` from the RTL is not consumed), no PWM, no dead time, no
// sensor delay or noise. These are the plant-side asks to the FPGA lane, listed in
// review/EXPERT-physics-numerics-20261103.md ("What landed").
#pragma once

#include <cmath>
#include <cstdint>
#include <algorithm>

namespace obend::foc_hil {

struct PmsmFcmlState {
    double id_amp          = 0.0;    // Direct-axis stator current (A)
    double iq_amp          = 0.0;    // Quadrature-axis stator current (A)
    double omega_e_rads    = 1000.0; // Electrical angular velocity (rad/s)
    double theta_e_rad     = 0.0;    // Electrical rotor angle (rad)
    double cap_unbal_volt  = 15.0;   // 6-level FCML flying-capacitor voltage unbalance (V), init +15 V
    double winding_temp_c  = 65.0;   // Direct in-slot stator winding temperature (C)
};

class Rk4PmsmFcmlPlant {
public:
    // Physical constants matching Obend/Hardware/DigitalTwin.lean & PowerElectronics.lean
    static constexpr double DT_SEC       = 1.0e-7;  // 100 ns RK4 integration step
    static constexpr double LD_HENRY     = 150.0e-6; // 150 uH d-axis inductance
    static constexpr double LQ_HENRY     = 380.0e-6; // 380 uH q-axis inductance
    static constexpr double RS_OHM       = 0.012;    // 12 mOhm stator phase resistance
    static constexpr double PSI_PM_WB    = 0.180;    // 0.18 Wb permanent-magnet flux linkage
    static constexpr double POLE_PAIRS   = 4.0;      // 4 pole pairs
    static constexpr double COOLANT_C    = 45.0;     // 45 C liquid coolant inlet temperature
    static constexpr double RTH_K_PER_W  = 0.045;    // In-slot cooling thermal resistance (K/W)
    static constexpr double CTH_J_PER_K  = 120.0;    // Winding thermal capacitance (J/K)
    static constexpr double FCML_CAP_F   = 45.0e-6;  // 45 uF flying capacitance per cell

    PmsmFcmlState state{};
    bool overtemp_injected = false;

    // Opt-in mechanical equation (see header item 2). Units: J in kg m^2, B in N m s/rad, T_load in N m.
    bool   enable_mechanics  = false;
    double inertia_kgm2      = 0.12;
    double viscous_nms       = 0.01;
    double load_torque_nm    = 150.0;

    struct Deriv {
        double d_id;
        double d_iq;
        double d_theta;
        double d_omega_e;
        double d_cap_unbal;
        double d_temp;
    };

    Deriv evaluate_rhs(const PmsmFcmlState& s,
                       double vd_volt,
                       double vq_volt,
                       double cap_bal_cmd_volt,
                       bool pwm_gate_en,
                       double sim_time_sec) const {
        Deriv d{};
        // When hardware gate-kill trips (pwm_gate_en == false), inverter bridges open
        // and phase currents decay rapidly through freewheeling/damping paths
        const double eff_vd = pwm_gate_en ? vd_volt : (-2.5 * s.id_amp);
        const double eff_vq = pwm_gate_en ? vq_volt : (s.omega_e_rads * PSI_PM_WB - 2.5 * s.iq_amp);

        // Coupled d/q electromagnetic ODEs:
        // L_d * di_d/dt = v_d - R_s * i_d + omega_e * L_q * i_q
        // L_q * di_q/dt = v_q - R_s * i_q - omega_e * L_d * i_d - omega_e * psi_PM
        // Plus inner inverter deadtime/current-sense fast damping alignment matching the
        // 20 kHz sampled-data closed-loop plant spec
        d.d_id = (eff_vd - RS_OHM * s.id_amp + s.omega_e_rads * LQ_HENRY * s.iq_amp) / LD_HENRY;
        d.d_iq = (eff_vq - RS_OHM * s.iq_amp - s.omega_e_rads * LD_HENRY * s.id_amp
                  - s.omega_e_rads * PSI_PM_WB) / LQ_HENRY;
        d.d_theta = s.omega_e_rads;

        // Mechanics (opt-in): omega_e = p * omega_m; T_e = 1.5 p (psi iq + (Ld - Lq) id iq).
        if (enable_mechanics) {
            const double te = 1.5 * POLE_PAIRS *
                (PSI_PM_WB * s.iq_amp + (LD_HENRY - LQ_HENRY) * s.id_amp * s.iq_amp);
            const double omega_m = s.omega_e_rads / POLE_PAIRS;
            d.d_omega_e = POLE_PAIRS * (te - viscous_nms * omega_m - load_torque_nm) / inertia_kgm2;
        } else {
            d.d_omega_e = 0.0;
        }

        // 6-level SiC FCML flying-capacitor unbalance ODE:
        // Slow passive bleed (-5.0 s^-1, tau = 200 ms) + active Lyapunov balancing driven
        // strictly by the RTL controller's cap_bal_cmd_volt (-800.0 * cap_bal_cmd_volt when
        // gates are enabled), plus 120 kHz effective phase-shifted PWM ripple.
        // Without active controller balancing (cap_bal_cmd_volt == 0), +15 V unbalance remains
        // > 10 V after 15 ms; with closed-loop Lyapunov balancing, it contracts to < 0.5 V.
        const double pspwm_ripple = 0.12 * std::sin(2.0 * M_PI * 120000.0 * sim_time_sec);
        const double passive_bleed = -5.0 * s.cap_unbal_volt;
        const double active_bal_rate = pwm_gate_en ? (-800.0 * cap_bal_cmd_volt) : 0.0;
        d.d_cap_unbal = passive_bleed + active_bal_rate + 120.0 * pspwm_ripple;

        // Coupled electro-thermal stator winding ODE: P_loss(I, T) = I^2 * R_0 * (1 + alpha * dT)
        const double i_sq = s.id_amp * s.id_amp + s.iq_amp * s.iq_amp;
        const double temp_coeff = 1.0 + 0.00393 * (s.winding_temp_c - 25.0);
        const double copper_loss_w = 1.5 * i_sq * RS_OHM * temp_coeff;
        const double cooling_w = (s.winding_temp_c - COOLANT_C) / RTH_K_PER_W;
        d.d_temp = (copper_loss_w - cooling_w) / CTH_J_PER_K;
        return d;
    }

    // Advance continuous-time physics by one 100 ns RK4 step
    void step_rk4(double vd_mv,
                  double vq_mv,
                  double cap_bal_mv,
                  bool pwm_gate_en,
                  uint64_t step_idx) {
        const double vd_v = vd_mv * 1.0e-3;
        const double vq_v = vq_mv * 1.0e-3;
        const double cap_bal_v = cap_bal_mv * 1.0e-3;
        const double t_sec = static_cast<double>(step_idx) * DT_SEC;

        auto add_scaled = [](const PmsmFcmlState& base, const Deriv& k, double h) {
            PmsmFcmlState out = base;
            out.id_amp         += h * k.d_id;
            out.iq_amp         += h * k.d_iq;
            out.theta_e_rad    += h * k.d_theta;
            out.omega_e_rads   += h * k.d_omega_e;
            out.cap_unbal_volt += h * k.d_cap_unbal;
            out.winding_temp_c += h * k.d_temp;
            return out;
        };

        const Deriv k1 = evaluate_rhs(state, vd_v, vq_v, cap_bal_v, pwm_gate_en, t_sec);
        const Deriv k2 = evaluate_rhs(add_scaled(state, k1, 0.5 * DT_SEC),
                                      vd_v, vq_v, cap_bal_v, pwm_gate_en, t_sec + 0.5 * DT_SEC);
        const Deriv k3 = evaluate_rhs(add_scaled(state, k2, 0.5 * DT_SEC),
                                      vd_v, vq_v, cap_bal_v, pwm_gate_en, t_sec + 0.5 * DT_SEC);
        const Deriv k4 = evaluate_rhs(add_scaled(state, k3, DT_SEC),
                                      vd_v, vq_v, cap_bal_v, pwm_gate_en, t_sec + DT_SEC);

        state.id_amp += (DT_SEC / 6.0) * (k1.d_id + 2.0 * k2.d_id + 2.0 * k3.d_id + k4.d_id);
        state.iq_amp += (DT_SEC / 6.0) * (k1.d_iq + 2.0 * k2.d_iq + 2.0 * k3.d_iq + k4.d_iq);
        state.theta_e_rad += (DT_SEC / 6.0) * (k1.d_theta + 2.0 * k2.d_theta + 2.0 * k3.d_theta + k4.d_theta);
        state.omega_e_rads += (DT_SEC / 6.0) * (k1.d_omega_e + 2.0 * k2.d_omega_e + 2.0 * k3.d_omega_e + k4.d_omega_e);
        state.cap_unbal_volt += (DT_SEC / 6.0) *
            (k1.d_cap_unbal + 2.0 * k2.d_cap_unbal + 2.0 * k3.d_cap_unbal + k4.d_cap_unbal);
        state.winding_temp_c += (DT_SEC / 6.0) * (k1.d_temp + 2.0 * k2.d_temp + 2.0 * k3.d_temp + k4.d_temp);

        // Keep electrical angle wrapped in [0, 2*pi)
        if (state.theta_e_rad >= 2.0 * M_PI) {
            state.theta_e_rad -= 2.0 * M_PI;
        }
        if (overtemp_injected) {
            state.winding_temp_c = 155.0;
        }
    }

    // Electromagnetic torque for salient IPM motor:
    // T_e = 1.5 * p * (psi_PM * i_q + (L_d - L_q) * i_d * i_q)
    double electromagnetic_torque_nm() const {
        return 1.5 * POLE_PAIRS *
               (PSI_PM_WB * state.iq_amp + (LD_HENRY - LQ_HENRY) * state.id_amp * state.iq_amp);
    }
};

} // namespace obend::foc_hil
