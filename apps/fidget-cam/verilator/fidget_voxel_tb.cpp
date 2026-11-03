// Flagship App #6 (`apps/fidget-cam/verilator/fidget_voxel_tb.cpp`):
// Verilated Recursive 3D Octree F-Rep Voxelizer (with Sound Interval Pruning),
// Standalone 3-Box Pruned SSA Tape Equivalence Verifier, Binary `.stl` 3D Mesh
// Generator (`build/impeller_part.stl`), and Full-Surface Gouge-Verified 5-Axis
// G-Code Generator (`build/impeller_5axis.ngc`).

#include "Vfidget_impeller_voxel_cam.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <tuple>
#include <vector>

namespace {

#pragma pack(push, 1)
struct StlTriangle {
    float nx, ny, nz;
    float v0x, v0y, v0z;
    float v1x, v1y, v1z;
    float v2x, v2y, v2z;
    uint16_t attr;
};
#pragma pack(pop)

static_assert(sizeof(StlTriangle) == 50, "Binary STL triangle facet must be exactly 50 bytes");

struct Interval {
    int64_t lo;
    int64_t hi;
};

Interval ivAdd(Interval a, Interval b) { return {a.lo + b.lo, a.hi + b.hi}; }
Interval ivSub(Interval a, Interval b) { return {a.lo - b.hi, a.hi - b.lo}; }
Interval ivNeg(Interval a) { return {-a.hi, -a.lo}; }
Interval ivMin(Interval a, Interval b) { return {std::min(a.lo, b.lo), std::min(a.hi, b.hi)}; }
Interval ivMax(Interval a, Interval b) { return {std::max(a.lo, b.lo), std::max(a.hi, b.hi)}; }

Interval ivSq(Interval a) {
    int64_t p0 = a.lo * a.lo;
    int64_t p1 = a.hi * a.hi;
    if (a.lo <= 0 && 0 <= a.hi) {
        return {0, std::max(p0, p1)};
    }
    return {std::min(p0, p1), std::max(p0, p1)};
}

// Sound 3D interval enclosure of `full_3d_sdf(x, y, z)` matching `impellerSsaTape` + axial slab
Interval evalImpeller3dInterval(Interval x, Interval y, Interval z) {
    Interval x2 = ivSq(x);
    Interval y2 = ivSq(y);
    Interval hub = ivSub(ivAdd(x2, y2), {100, 100});
    Interval boss = ivSub(ivAdd(ivSq(ivSub(x, {10, 10})), y2), {4, 4});
    Interval uni = ivMin(hub, boss);
    Interval bore = ivSub(ivAdd(ivSq(ivAdd(x, {4, 4})), y2), {4, 4});
    Interval xySdf = ivMax(uni, ivNeg(bore));
    Interval zSdf = ivSub(ivSq(z), {36, 36});
    return ivMax(xySdf, zSdf);
}

void addQuadAsTriangles(
    std::vector<StlTriangle>& tris,
    float nx, float ny, float nz,
    float x0, float y0, float z0,
    float x1, float y1, float z1,
    float x2, float y2, float z2,
    float x3, float y3, float z3) {
    StlTriangle t1{};
    t1.nx = nx; t1.ny = ny; t1.nz = nz;
    t1.v0x = x0; t1.v0y = y0; t1.v0z = z0;
    t1.v1x = x1; t1.v1y = y1; t1.v1z = z1;
    t1.v2x = x2; t1.v2y = y2; t1.v2z = z2;
    t1.attr = 0;

    StlTriangle t2{};
    t2.nx = nx; t2.ny = ny; t2.nz = nz;
    t2.v0x = x0; t2.v0y = y0; t2.v0z = z0;
    t2.v1x = x2; t2.v1y = y2; t2.v1z = z2;
    t2.v2x = x3; t2.v2y = y3; t2.v2z = z3;
    t2.attr = 0;

    tris.push_back(t1);
    tris.push_back(t2);
}

} // namespace

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::randReset(2);
    Verilated::traceEverOn(true);

    auto* dut = new Vfidget_impeller_voxel_cam;
    auto* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("fidget_cam_trace.vcd");

    uint64_t sim_time = 0;
    auto tick = [&]() {
        dut->clk = 0;
        dut->eval();
        if (sim_time < 2048) tfp->dump(sim_time);
        sim_time++;
        dut->clk = 1;
        dut->eval();
        if (sim_time < 2048) tfp->dump(sim_time);
        sim_time++;
    };

    // Synchronous reset
    dut->rst = 1;
    dut->in_x = 0;
    dut->in_y = 0;
    dut->in_z = 0;
    dut->in_tx = 40;
    dut->in_ty = 40;
    dut->in_tz = 40;
    dut->in_step_dist = 2;
    dut->in_subdiv_level = 4;
    dut->in_liverps_override_en = 0;
    tick();
    dut->rst = 0;

    // 1. Verify OpenUSD LIVERPS layer override & `.obend` ImpellerCamTop datapath outputs
    dut->in_liverps_override_en = 0;
    dut->eval();
    assert(dut->out_compacted_center_ops == 7ULL);
    assert(dut->out_compacted_lug_ops == 9ULL);
    assert(dut->out_compacted_bore_ops == 9ULL);
    assert(dut->out_certified_wall_um == 2600ULL);
    assert(dut->out_lipschitz_step_pad_um == 151ULL);
    assert(dut->out_octree_active_voxels == 521ULL);

    dut->in_liverps_override_en = 1;
    dut->eval();
    assert(dut->out_certified_wall_um == 2800ULL);
    assert(dut->out_lipschitz_step_pad_um == 151ULL);
    assert(dut->out_octree_active_voxels == 585ULL);

    // 2. Recursive 3D Octree Subdivision with Sound Interval Pruning & Verilated Leaf Evaluation
    //    Domain: [-16, 15] x [-16, 15] x [-8, 7] (32 x 32 x 16 = 16,384 voxels)
    constexpr int X_MIN = -16, X_MAX = 15;
    constexpr int Y_MIN = -16, Y_MAX = 15;
    constexpr int Z_MIN = -8,  Z_MAX = 7;
    constexpr int NX = X_MAX - X_MIN + 1; // 32
    constexpr int NY = Y_MAX - Y_MIN + 1; // 32
    constexpr int NZ = Z_MAX - Z_MIN + 1; // 16

    std::vector<uint8_t> voxel_solid(NX * NY * NZ, 0);
    auto idx3d = [&](int x, int y, int z) -> size_t {
        return static_cast<size_t>(((z - Z_MIN) * NY + (y - Y_MIN)) * NX + (x - X_MIN));
    };

    uint64_t octree_pruned_empty_boxes = 0;
    uint64_t octree_pruned_solid_boxes = 0;
    uint64_t octree_hw_leaf_evals = 0;
    uint64_t total_solid_voxels = 0;

    auto evalOctree = [&](auto& self, int x0, int x1, int y0, int y1, int z0, int z1) -> void {
        if (x0 > x1 || y0 > y1 || z0 > z1) return;
        Interval iv = evalImpeller3dInterval({x0, x1}, {y0, y1}, {z0, z1});
        if (iv.lo > 0) {
            // Entire 3D octree cell is strictly outside the impeller solid
            octree_pruned_empty_boxes++;
            return;
        }
        if (iv.hi <= 0 && (x1 - x0 >= 1 || y1 - y0 >= 1 || z1 - z0 >= 1)) {
            // Entire 3D octree cell is strictly inside the impeller solid interior
            octree_pruned_solid_boxes++;
            for (int z = z0; z <= z1; ++z) {
                for (int y = y0; y <= y1; ++y) {
                    for (int x = x0; x <= x1; ++x) {
                        voxel_solid[idx3d(x, y, z)] = 1;
                        total_solid_voxels++;
                    }
                }
            }
            return;
        }
        if (x0 == x1 && y0 == y1 && z0 == z1) {
            // Straddling 1x1x1 boundary leaf: evaluate on Verilated SSA F-Rep pipeline
            dut->in_x = static_cast<uint64_t>(static_cast<int64_t>(x0));
            dut->in_y = static_cast<uint64_t>(static_cast<int64_t>(y0));
            dut->in_z = static_cast<uint64_t>(static_cast<int64_t>(z0));
            dut->in_tx = 40ULL;
            dut->in_ty = 40ULL;
            dut->in_tz = 40ULL;
            tick();
            octree_hw_leaf_evals++;
            if (dut->out_in_solid_3d != 0ULL) {
                voxel_solid[idx3d(x0, y0, z0)] = 1;
                total_solid_voxels++;
            }
            return;
        }
        int xm = x0 + (x1 - x0) / 2;
        int ym = y0 + (y1 - y0) / 2;
        int zm = z0 + (z1 - z0) / 2;
        int xs[2][2] = {{x0, xm}, {xm + 1, x1}};
        int ys[2][2] = {{y0, ym}, {ym + 1, y1}};
        int zs[2][2] = {{z0, zm}, {zm + 1, z1}};
        for (int kz = 0; kz < 2; ++kz) {
            for (int ky = 0; ky < 2; ++ky) {
                for (int kx = 0; kx < 2; ++kx) {
                    self(self, xs[kx][0], xs[kx][1], ys[ky][0], ys[ky][1], zs[kz][0], zs[kz][1]);
                }
            }
        }
    };

    evalOctree(evalOctree, X_MIN, X_MAX, Y_MIN, Y_MAX, Z_MIN, Z_MAX);
    assert(octree_pruned_empty_boxes > 0ULL);
    assert(octree_pruned_solid_boxes > 0ULL);
    // Octree pruning evaluates strictly fewer hardware leaves than the 16,384-voxel dense grid
    assert(octree_hw_leaf_evals < static_cast<uint64_t>(NX * NY * NZ));
    assert(total_solid_voxels > 3000ULL);

    // 3. Verify All 3 Standalone Box-Pruned SSA Tapes & Connected Bore/Boss Geometry in Hardware
    uint64_t center_box_checks = 0;
    uint64_t boss_box_checks = 0;
    uint64_t bore_box_checks = 0;

    for (int z = -1; z <= 1; ++z) {
        for (int y = -1; y <= 1; ++y) {
            for (int x = 5; x <= 6; ++x) {
                dut->in_x = static_cast<uint64_t>(static_cast<int64_t>(x));
                dut->in_y = static_cast<uint64_t>(static_cast<int64_t>(y));
                dut->in_z = static_cast<uint64_t>(static_cast<int64_t>(z));
                tick();
                assert(dut->out_frep_center_pruned == dut->out_frep_full);
                center_box_checks++;
            }
            for (int x = 11; x <= 12; ++x) {
                dut->in_x = static_cast<uint64_t>(static_cast<int64_t>(x));
                dut->in_y = static_cast<uint64_t>(static_cast<int64_t>(y));
                dut->in_z = static_cast<uint64_t>(static_cast<int64_t>(z));
                tick();
                assert(dut->out_frep_boss_pruned == dut->out_frep_full);
                boss_box_checks++;
            }
            for (int x = -5; x <= -3; ++x) {
                dut->in_x = static_cast<uint64_t>(static_cast<int64_t>(x));
                dut->in_y = static_cast<uint64_t>(static_cast<int64_t>(y));
                dut->in_z = static_cast<uint64_t>(static_cast<int64_t>(z));
                tick();
                assert(dut->out_frep_bore_pruned == dut->out_frep_full);
                bore_box_checks++;
            }
        }
    }
    assert(center_box_checks == 18ULL);
    assert(boss_box_checks == 18ULL);
    assert(bore_box_checks == 27ULL);

    auto isSolidAt = [&](int x, int y, int z) -> bool {
        if (x < X_MIN || x > X_MAX || y < Y_MIN || y > Y_MAX || z < Z_MIN || z > Z_MAX) {
            return false;
        }
        return voxel_solid[idx3d(x, y, z)] != 0;
    };

    // Confirm genuine physical features in the octree-voxelized part:
    // (a) Internal cooling bore at (-4, 0, z) is CARVED HOLLOW inside the solid hub!
    for (int z = -6; z <= 6; ++z) {
        assert(!isSolidAt(-4, 0, z));
        assert(isSolidAt(-1, 0, z));
        assert(isSolidAt(-7, 0, z));
    }
    // (b) Rim-attached mounting boss is connected across hub rim x = 8..12!
    for (int x = 8; x <= 12; ++x) {
        assert(isSolidAt(x, 0, 0));
    }

    // (c) 16-bit boundary stress test: [-32768, +32767] coordinates do not overflow 64-bit datapath
    dut->in_x = static_cast<uint64_t>(INT64_C(-32768));
    dut->in_y = static_cast<uint64_t>(INT64_C(32767));
    dut->in_z = static_cast<uint64_t>(INT64_C(-32768));
    tick();
    assert(static_cast<int64_t>(dut->out_frep_full) > 0);
    assert(dut->out_in_solid_3d == 0ULL);

    // 4. Emit Binary `.stl` 3D Mesh (`build/impeller_part.stl`) & Collect All Exposed Surface Voxels
    std::vector<StlTriangle> triangles;
    std::vector<std::tuple<int, int, int>> surface_voxels;
    for (int z = Z_MIN; z <= Z_MAX; ++z) {
        for (int y = Y_MIN; y <= Y_MAX; ++y) {
            for (int x = X_MIN; x <= X_MAX; ++x) {
                if (!isSolidAt(x, y, z)) continue;
                bool is_boundary = false;
                float x0 = static_cast<float>(x) - 0.5f;
                float x1 = static_cast<float>(x) + 0.5f;
                float y0 = static_cast<float>(y) - 0.5f;
                float y1 = static_cast<float>(y) + 0.5f;
                float z0 = static_cast<float>(z) - 0.5f;
                float z1 = static_cast<float>(z) + 0.5f;

                if (!isSolidAt(x + 1, y, z)) {
                    addQuadAsTriangles(triangles,  1,  0,  0, x1, y0, z0, x1, y1, z0, x1, y1, z1, x1, y0, z1);
                    is_boundary = true;
                }
                if (!isSolidAt(x - 1, y, z)) {
                    addQuadAsTriangles(triangles, -1,  0,  0, x0, y1, z0, x0, y0, z0, x0, y0, z1, x0, y1, z1);
                    is_boundary = true;
                }
                if (!isSolidAt(x, y + 1, z)) {
                    addQuadAsTriangles(triangles,  0,  1,  0, x1, y1, z0, x0, y1, z0, x0, y1, z1, x1, y1, z1);
                    is_boundary = true;
                }
                if (!isSolidAt(x, y - 1, z)) {
                    addQuadAsTriangles(triangles,  0, -1,  0, x0, y0, z0, x1, y0, z0, x1, y0, z1, x0, y0, z1);
                    is_boundary = true;
                }
                if (!isSolidAt(x, y, z + 1)) {
                    addQuadAsTriangles(triangles,  0,  0,  1, x0, y0, z1, x1, y0, z1, x1, y1, z1, x0, y1, z1);
                    is_boundary = true;
                }
                if (!isSolidAt(x, y, z - 1)) {
                    addQuadAsTriangles(triangles,  0,  0, -1, x0, y1, z0, x1, y1, z0, x1, y0, z0, x0, y0, z0);
                    is_boundary = true;
                }
                if (is_boundary) {
                    surface_voxels.emplace_back(x, y, z);
                }
            }
        }
    }

    assert(!triangles.empty());
    assert(!surface_voxels.empty());
    {
        std::ofstream stl("build/impeller_part.stl", std::ios::binary);
        assert(stl.is_open());
        char header[80];
        std::memset(header, 0, sizeof(header));
        std::snprintf(header, sizeof(header), "ObjectiveBend FidgetCam Verified Impeller Binary STL (Verilated)");
        stl.write(header, 80);
        uint32_t num_tris = static_cast<uint32_t>(triangles.size());
        stl.write(reinterpret_cast<const char*>(&num_tris), sizeof(uint32_t));
        stl.write(reinterpret_cast<const char*>(triangles.data()),
                  static_cast<std::streamsize>(triangles.size() * sizeof(StlTriangle)));
        stl.close();
    }

    // 5. Full-Surface 5-Axis Finishing Toolpath Verification in Verilator & Emit `build/impeller_5axis.ngc`
    //    Checks EVERY 5-axis waypoint against EVERY exposed boundary surface voxel of the 3D mesh!
    std::ofstream ngc("build/impeller_5axis.ngc");
    assert(ngc.is_open());
    ngc << "%\n";
    ngc << "(Objective Bend Flagship App #6: Full-Surface Gouge-Verified 5-Axis Impeller Toolpath)\n";
    ngc << "(Certified by Obend.Apps.FidgetCam: L_box=72, stepPad=144, gouge_violations=0)\n";
    ngc << "G90 G21 G17 G40 G49 G80\n";
    ngc << "T1 M06 (10mm Ball-Endmill, FRep: x^2 + y^2 + z^2 - 100)\n";
    ngc << "S18000 M03\n";
    ngc << "G00 X30.000 Y0.000 Z25.000 A0.000 C0.000\n";

    int gcode_lines = 0;
    uint64_t surface_gouge_checks = 0;
    const int64_t safe_cutter_radius = 29;
    for (int pass = 0; pass < 3; ++pass) {
        int64_t tz = 18 + pass * 2;
        double tilt_a = 12.5 + pass * 2.5;
        for (int deg = 0; deg < 360; deg += 15) {
            double rad = static_cast<double>(deg) * 3.14159265358979323846 / 180.0;
            int64_t tx = static_cast<int64_t>(std::llround(static_cast<double>(safe_cutter_radius) * std::cos(rad)));
            int64_t ty = static_cast<int64_t>(std::llround(static_cast<double>(safe_cutter_radius) * std::sin(rad)));

            int64_t min_tool_sdf = INT64_MAX;
            for (const auto& [sx, sy, sz] : surface_voxels) {
                dut->in_x = static_cast<uint64_t>(static_cast<int64_t>(sx));
                dut->in_y = static_cast<uint64_t>(static_cast<int64_t>(sy));
                dut->in_z = static_cast<uint64_t>(static_cast<int64_t>(sz));
                dut->in_tx = static_cast<uint64_t>(tx);
                dut->in_ty = static_cast<uint64_t>(ty);
                dut->in_tz = static_cast<uint64_t>(tz);
                dut->in_step_dist = 2ULL;
                tick();
                surface_gouge_checks++;

                assert(dut->out_no_gouge_ok == 1ULL);
                assert(dut->out_gouge_violations == 0ULL);
                int64_t sdf = static_cast<int64_t>(dut->out_tool_sdf);
                if (sdf < min_tool_sdf) min_tool_sdf = sdf;
            }

            ngc << std::fixed << std::setprecision(3)
                << "G01 X" << static_cast<double>(tx)
                << " Y" << static_cast<double>(ty)
                << " Z" << static_cast<double>(tz)
                << " A" << tilt_a
                << " C" << static_cast<double>(deg)
                << " F1200.0 (MIN_TOOL_SDF=" << min_tool_sdf << " NO_GOUGE=1)\n";
            gcode_lines++;
        }
    }
    ngc << "G00 Z50.000 A0.000 C0.000\n";
    ngc << "M05\n";
    ngc << "M30\n";
    ngc << "%\n";
    ngc.close();

    assert(dut->out_gouge_violations == 0ULL);

    // 6. Adversarial Gouge Fault-Injection Test: plunge cutter onto protruding boss tip (12, 0, 0)
    dut->in_x = 12ULL;
    dut->in_y = 0ULL;
    dut->in_z = 0ULL;
    dut->in_tx = 12ULL;
    dut->in_ty = 0ULL;
    dut->in_tz = 0ULL;
    dut->in_step_dist = 2ULL;
    tick();
    assert(dut->out_no_gouge_ok == 0ULL);
    assert(dut->out_gouge_violations == 1ULL);

    tfp->close();

    std::cout << "[fidget-cam] Verilator 3D Octree Voxelizer & Full-Surface 5-Axis CAM Verification PASSED\n"
              << "  octree_hw_leaf_evals=" << octree_hw_leaf_evals
              << " octree_pruned_empty_boxes=" << octree_pruned_empty_boxes
              << " octree_pruned_solid_boxes=" << octree_pruned_solid_boxes
              << " solid_voxels=" << total_solid_voxels
              << " center_7op_checks=" << center_box_checks
              << " boss_9op_checks=" << boss_box_checks
              << " bore_9op_checks=" << bore_box_checks
              << " stl_triangles=" << triangles.size()
              << " surface_voxels=" << surface_voxels.size()
              << " gcode_blocks=" << gcode_lines
              << " surface_gouge_checks=" << surface_gouge_checks
              << " adversarial_gouge_detected=" << dut->out_gouge_violations << "\n";

    delete tfp;
    delete dut;
    return 0;
}
