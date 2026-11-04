#!/usr/bin/env python
"""The untrusted producer for `devsim-dd1d@1` (lean/Obend/Hardware/Device/DriftDiffusion.lean).

Runs the sky130-derived diode recipe (the same steps as `Obend.Hardware.Device.Sky130Diode`), builds
the 1D mesh, solves Poisson + Scharfetter-Gummel continuity with Caughey-Thomas mobility and SRH in
devsim 2.11.2, and writes, per bias point, the object (`spec_*.json`) and the certificate
(`cert_*.json`) the Lean checker reads. Nothing here is trusted: every number in the certificate is
re-derived or bracketed by the kernel-side checker.

    ~/tools/devsim/.venv/bin/python -I run_diode.py --out ../certs [--pwell-dose 2.6e13]

Units: cm, s, V, A, K, eV (devsim's). Decimal output: mpmath values to 30 significant digits, the
double-precision solution by shortest round-trip repr.
"""
import argparse
import json
import math
import os
import sys
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 50

# ---------------------------------------------------------------------------------------------
# Constants (Obend.Hardware.Device.Constants; sources there)
# ---------------------------------------------------------------------------------------------
SI = dict(tempK="300", epsR="11.9", eps0="8.8541878128e-14", q="1.602176634e-19", kB="1.380649e-23",
          nc="2.86e19", nv="3.10e19", egEv="1.1242")
CT_N = dict(muMin="65", muMax="1330", nRef="8.5e16", alphaNum=18, alphaDen=25)
CT_P = dict(muMin="47.7", muMax="495", nRef="6.3e16", alphaNum=19, alphaDen=25)
TAU_N = "1.0e-5"
TAU_P = "1.0e-5"
# Plummer Table 7-5 (D0 cm^2/s, EA eV)
DIFF = {"B": ("1.0", "3.5"), "P": ("4.70", "3.68"), "As": ("9.17", "3.99"), "Sb": ("4.58", "3.88")}
# Plummer Table 6-? Deal-Grove fits, (100) silicon (C2/1.68); um^2/h and um/h -> cm^2/s and cm/s
UM2_PER_H = mp.mpf("1.0e-8") / 3600
UM_PER_H = mp.mpf("1.0e-4") / 3600
DEAL_GROVE = {
    "dry": (mp.mpf(772) * UM2_PER_H, mp.mpf("1.23"), mp.mpf("6.23e6") / mp.mpf("1.68") * UM_PER_H, mp.mpf("2.0")),
    "wet": (mp.mpf(386) * UM2_PER_H, mp.mpf("0.78"), mp.mpf("1.63e8") / mp.mpf("1.68") * UM_PER_H, mp.mpf("2.05")),
}
SI_PER_OXIDE = mp.mpf("0.44")
# Plummer ch. 8 range table (keV, Rp nm, dRp nm)
RANGE = {
    "P": [(10, 19.9, 6.4), (20, 34.2, 12.5), (30, 47.3, 17.9), (40, 59.8, 22.9), (50, 71.7, 27.5), (60, 83.3, 31.7),
          (70, 94.7, 35.6), (80, 105, 39.3), (90, 116, 42.8), (100, 127, 46.1), (120, 148, 52.2), (140, 169, 57.9),
          (160, 189, 63.0), (180, 210, 67.8), (200, 229, 72.3)],
    "As": [(10, 8.4, 4.3), (20, 15.6, 7.5), (30, 22.6, 10.2), (40, 29.4, 12.8), (50, 36.2, 15.2), (60, 42.9, 17.6),
           (70, 49.5, 19.8), (80, 56.1, 22.0), (90, 62.6, 24.1), (100, 69.2, 26.1), (120, 82.1, 30.1), (140, 95.0, 33.9),
           (160, 107, 37.5), (180, 120, 41.1), (200, 133, 44.6)],
    "Sb": [(10, 12.1, 5.8), (20, 21.9, 10.0), (30, 30.6, 13.3), (40, 38.5, 16.2), (50, 45.9, 18.7), (60, 52.8, 20.9),
           (70, 59.4, 22.9), (80, 65.6, 24.8), (90, 71.6, 26.5), (100, 77.3, 28.0), (120, 88.3, 30.9), (140, 98.5, 33.4),
           (160, 108, 35.7), (180, 117, 37.8), (200, 126, 39.7)],
    "B": [(10, 47.3, 24.9), (20, 82.6, 38.4), (30, 114, 48.3), (40, 143, 56.2), (50, 171, 62.8), (60, 198, 68.5),
          (70, 223, 73.6), (80, 248, 78.0), (90, 272, 82.1), (100, 296, 85.7), (120, 341, 92.2), (140, 385, 97.8),
          (160, 428, 102), (180, 469, 107), (200, 509, 110)],
}
DONOR = {"B": False, "P": True, "As": True, "Sb": True}

q = mp.mpf(SI["q"])
kB = mp.mpf(SI["kB"])
kB_eV = kB / q
T = mp.mpf(SI["tempK"])
VT = kB * T / q
EPS = mp.mpf(SI["epsR"]) * mp.mpf(SI["eps0"])
NI = mp.sqrt(mp.mpf(SI["nc"]) * mp.mpf(SI["nv"]) * mp.exp(-mp.mpf(SI["egEv"]) / VT))


import re

_NUM = re.compile(r'"(-?\d[\d]*(?:\.\d+)?(?:[eE][+-]?\d+)?)"')


def dump_numbers(obj, f):
    """json.dump, with every numeric-looking string written as a JSON number (exact decimals)."""
    f.write(_NUM.sub(r"\1", json.dumps(obj, separators=(",", ":"))))


def dec(v, digits=30):
    """A decimal string of an mpmath value, exact enough for the checker's brackets."""
    return mp.nstr(mp.mpf(v), digits, strip_zeros=True, min_fixed=-1, max_fixed=0)


def range_at(sp, kev):
    rows = RANGE[sp]
    for (k1, r1, d1), (k2, r2, d2) in zip(rows, rows[1:]):
        if k1 <= kev <= k2:
            f = mp.mpf(kev - k1) / (k2 - k1)
            nm = mp.mpf("1e-7")
            return (mp.mpf(r1) + f * (mp.mpf(r2) - r1)) * nm, (mp.mpf(d1) + f * (mp.mpf(d2) - d1)) * nm
    raise ValueError(f"{sp} {kev} keV outside the range table")


def arrhenius(d0, ea, tempK):
    return mp.mpf(d0) * mp.exp(-mp.mpf(ea) / (kB_eV * mp.mpf(tempK)))


def diffusivities(tempK):
    return {sp: arrhenius(d0, ea, tempK) for sp, (d0, ea) in DIFF.items()}


# ---------------------------------------------------------------------------------------------
# The wafer and the recipe (mirror of Obend.Hardware.Device.Wafer)
# ---------------------------------------------------------------------------------------------
class Wafer:
    def __init__(self, background):
        self.background = mp.mpf(background)
        self.films = []  # (material, thickness) top first
        self.dopants = []  # dict(species, dose, rp, var)
        self.removed = mp.mpf(0)

    def films_thickness(self):
        return sum((t for _, t in self.films), mp.mpf(0))

    def top_oxide(self):
        return self.films[0][1] if self.films and self.films[0][0] == "oxide" else mp.mpf(0)

    def implant(self, sp, kev, dose):
        rp, drp = range_at(sp, kev)
        self.dopants.insert(0, dict(species=sp, dose=mp.mpf(dose), rp=rp - self.films_thickness(), var=drp * drp))

    def anneal(self, D, timeS):
        for g in self.dopants:
            g["var"] = g["var"] + 2 * D[g["species"]] * mp.mpf(timeS)

    def oxidize(self, amb, tempK, timeS):
        c1, e1, c2, e2 = DEAL_GROVE[amb]
        B = arrhenius(c1, e1, tempK)
        BA = arrhenius(c2, e2, tempK)
        A = B / BA
        x0 = self.top_oxide()
        tau = (x0 * x0 + A * x0) / B
        target = B * (mp.mpf(timeS) + tau)
        x_new = (-A + mp.sqrt(A * A + 4 * target)) / 2
        D = diffusivities(tempK)
        self.anneal(D, timeS)
        consumed = SI_PER_OXIDE * (x_new - x0)
        for g in self.dopants:
            g["rp"] = g["rp"] - consumed
        self.removed += consumed
        if self.films and self.films[0][0] == "oxide":
            self.films[0] = ("oxide", x_new)
        else:
            self.films.insert(0, ("oxide", x_new))
        return B, BA, x_new, D

    def deposit(self, m, t):
        t = mp.mpf(t)
        if self.films and self.films[0][0] == m:
            self.films[0] = (m, self.films[0][1] + t)
        else:
            self.films.insert(0, (m, t))

    def strip(self, m):
        assert self.films and self.films[0][0] == m, f"strip {m}: top film is {self.films[:1]}"
        self.films.pop(0)

    def net_doping(self, x):
        n = self.background
        for g in self.dopants:
            n += (1 if DONOR[g["species"]] else -1) * self.component(g, x)
        return n

    def total_doping(self, x):
        n = abs(self.background)
        for g in self.dopants:
            n += abs(self.component(g, x))
        return n

    @staticmethod
    def component(g, x):
        x = mp.mpf(x)
        peak = g["dose"] / mp.sqrt(2 * mp.pi * g["var"])
        return peak * (mp.exp(-(x - g["rp"]) ** 2 / (2 * g["var"])) + mp.exp(-(x + g["rp"]) ** 2 / (2 * g["var"])))


def d_json(D):
    return {sp: dec(v) for sp, v in D.items()}


def run_recipe(steps, background):
    """Execute the recipe; return the wafer, the JSON recipe, the JSON step certificates."""
    w = Wafer(background)
    recipe, certs = [], []
    for st in steps:
        op = st[0]
        if op == "implant":
            _, sp, kev, dose = st
            w.implant(sp, kev, dose)
            recipe.append(dict(op="implant", species=sp, keV=str(kev), dose=str(dose)))
            certs.append(dict(kind="none"))
        elif op == "anneal":
            _, tempK, timeS = st
            D = diffusivities(tempK)
            w.anneal(D, timeS)
            recipe.append(dict(op="anneal", tempK=str(tempK), timeS=str(timeS)))
            certs.append(dict(kind="anneal", D=d_json(D)))
        elif op == "oxidize":
            _, amb, tempK, timeS = st
            B, BA, x_new, D = w.oxidize(amb, tempK, timeS)
            recipe.append(dict(op="oxidize", ambient=amb, tempK=str(tempK), timeS=str(timeS)))
            certs.append(dict(kind="oxidize", B=dec(B), BA=dec(BA), xNewCm=dec(x_new), D=d_json(D)))
        elif op == "deposit":
            _, m, t = st
            w.deposit(m, t)
            recipe.append(dict(op="deposit", film=m, thicknessCm=str(t)))
            certs.append(dict(kind="none"))
        elif op == "strip":
            _, m = st
            w.strip(m)
            recipe.append(dict(op="strip", film=m))
            certs.append(dict(kind="none"))
        else:
            raise ValueError(op)
    return w, recipe, certs


def sky130_recipe(pwell_dose="1.3e13", nplus_dose="1.0e15"):
    """The recipe of Obend.Hardware.Device.Sky130Diode (sources in that module)."""
    return [
        ("implant", "B", 160, pwell_dose),          # p-well: R_p 0.428 um ~ the public peak depth 0.42 um
        ("anneal", "1273.15", "1800"),               # well drive 1000 C 30 min: sigma -> 0.124 um ~ y.char 0.13 um
        ("oxidize", "dry", "1173.15", "3600"),       # screen oxide, dry O2 900 C 60 min (~9 nm)
        ("implant", "As", 50, nplus_dose),           # n+ through the screen oxide
        ("anneal", "1173.15", "1800"),               # activation 900 C 30 min
        ("strip", "oxide"),                          # contact opening
        ("deposit", "metal", "5e-5"),                # 0.5 um metal
    ]


# ---------------------------------------------------------------------------------------------
# The mesh
# ---------------------------------------------------------------------------------------------
def mesh_points(depth_cm, junction_cm=1.0e-5):
    """Node depths, the same for every dose (so a certificate of one device is judged on the other's
    mesh): 2 nm at the surface, 1 nm within 30 nm of the nominal 100 nm junction, graded to 25 nm."""
    xs = []
    x = 0.0
    while x < depth_cm - 1e-12:
        d = abs(x - junction_cm)
        if d < 0.03e-4:
            h = 1.0e-7
        elif x < 0.08e-4:
            h = 2.0e-7
        elif d < 0.1e-4:
            h = 2.5e-7
        elif d < 0.25e-4:
            h = 5.0e-7
        else:
            h = 25.0e-7
        xs.append(round(x, 12))
        x += h
    xs.append(depth_cm)
    return xs


def find_junction(w, depth_cm):
    xs = [i * 1e-7 for i in range(int(depth_cm / 1e-7))]
    prev = None
    for x in xs:
        n = w.net_doping(x)
        if prev is not None and (prev > 0) != (n > 0):
            return x
        prev = n
    raise RuntimeError("no junction")


# ---------------------------------------------------------------------------------------------
# devsim
# ---------------------------------------------------------------------------------------------
def solve_device(w, xs, biases, area_cm2, tag):
    import devsim as ds
    from devsim.python_packages.model_create import (CreateSolution, CreateNodeModel, CreateNodeModelDerivative,
                                                     CreateEdgeModel, CreateEdgeModelDerivatives,
                                                     CreateContactNodeModel, CreateContactNodeModelDerivative)
    from devsim.python_packages.simple_physics import (CreateSiliconPotentialOnly, CreateSiliconPotentialOnlyContact,
                                                       CreateSRH, CreatePE, CreateSiliconDriftDiffusionAtContact,
                                                       GetContactBiasName, ece_name, hce_name)
    from devsim.python_packages.simple_dd import CreateBernoulli, CreateElectronCurrent, CreateHoleCurrent

    dev, reg, mesh = f"diode_{tag}", "si", f"mesh_{tag}"
    ds.create_1d_mesh(mesh=mesh)
    # the mesh lines are given explicitly: one line per node, spacing ignored by giving each a ps
    for i, x in enumerate(xs):
        kw = dict(mesh=mesh, pos=x, ps=1.0)
        if i == 0:
            kw["tag"] = "top"
        elif i == len(xs) - 1:
            kw["tag"] = "bot"
        ds.add_1d_mesh_line(**kw)
    ds.add_1d_contact(mesh=mesh, name="top", tag="top", material="metal")
    ds.add_1d_contact(mesh=mesh, name="bot", tag="bot", material="metal")
    ds.add_1d_region(mesh=mesh, material="Si", region=reg, tag1="top", tag2="bot")
    ds.finalize_mesh(mesh=mesh)
    ds.create_device(mesh=mesh, device=dev)

    xnodes = list(ds.get_node_model_values(device=dev, region=reg, name="x"))
    assert len(xnodes) == len(xs), (len(xnodes), len(xs))
    for a, b in zip(xnodes, xs):
        assert abs(a - b) <= 1e-18 + 1e-12 * abs(b), (a, b)

    # parameters
    for name, val in [("Permittivity", float(EPS)), ("ElectronCharge", float(q)), ("n_i", float(NI)), ("T", float(T)),
                      ("kT", float(kB * T)), ("V_t", float(VT)), ("taun", float(TAU_N)), ("taup", float(TAU_P)),
                      ("n1", float(NI)), ("p1", float(NI)),
                      ("mu_min_n", float(CT_N["muMin"])), ("mu_max_n", float(CT_N["muMax"])), ("nref_n", float(CT_N["nRef"])),
                      ("alpha_n", CT_N["alphaNum"] / CT_N["alphaDen"]),
                      ("mu_min_p", float(CT_P["muMin"])), ("mu_max_p", float(CT_P["muMax"])), ("nref_p", float(CT_P["nRef"])),
                      ("alpha_p", CT_P["alphaNum"] / CT_P["alphaDen"])]:
        ds.set_parameter(device=dev, region=reg, name=name, value=val)

    # doping from the recipe, 30-digit decimals rounded to double for the solver
    net = [w.net_doping(x) for x in xs]
    tot = [w.total_doping(x) for x in xs]
    ds.node_solution(device=dev, region=reg, name="NetDoping")
    ds.set_node_values(device=dev, region=reg, name="NetDoping", values=[float(v) for v in net])
    ds.node_solution(device=dev, region=reg, name="TotalDoping")
    ds.set_node_values(device=dev, region=reg, name="TotalDoping", values=[float(v) for v in tot])

    # Caughey-Thomas node mobilities and their edge means
    CreateNodeModel(dev, reg, "mu_n_node", "mu_min_n + (mu_max_n - mu_min_n)/(1 + (TotalDoping/nref_n)^alpha_n)")
    CreateNodeModel(dev, reg, "mu_p_node", "mu_min_p + (mu_max_p - mu_min_p)/(1 + (TotalDoping/nref_p)^alpha_p)")
    ds.edge_from_node_model(device=dev, region=reg, node_model="mu_n_node")
    ds.edge_from_node_model(device=dev, region=reg, node_model="mu_p_node")
    CreateEdgeModel(dev, reg, "mu_n_edge", "0.5*(mu_n_node@n0 + mu_n_node@n1)")
    CreateEdgeModel(dev, reg, "mu_p_edge", "0.5*(mu_p_node@n0 + mu_p_node@n1)")

    # equilibrium potential first
    CreateSiliconPotentialOnly(dev, reg)
    for c in ("top", "bot"):
        ds.set_parameter(device=dev, name=GetContactBiasName(c), value=0.0)
        CreateSiliconPotentialOnlyContact(dev, reg, c)
    ds.solve(type="dc", absolute_error=1.0, relative_error=1e-12, maximum_iterations=50)

    # drift-diffusion
    CreateSolution(dev, reg, "Electrons")
    CreateSolution(dev, reg, "Holes")
    ds.set_node_values(device=dev, region=reg, name="Electrons", init_from="IntrinsicElectrons")
    ds.set_node_values(device=dev, region=reg, name="Holes", init_from="IntrinsicHoles")
    CreatePE(dev, reg)
    CreateBernoulli(dev, reg)
    CreateSRH(dev, reg)
    CreateElectronCurrent(dev, reg, "mu_n_edge")
    CreateHoleCurrent(dev, reg, "mu_p_edge")
    CreateNodeModel(dev, reg, "NCharge", "-ElectronCharge * Electrons")
    CreateNodeModelDerivative(dev, reg, "NCharge", "-ElectronCharge * Electrons", "Electrons")
    ds.equation(device=dev, region=reg, name=ece_name, variable_name="Electrons", time_node_model="NCharge",
                edge_model="ElectronCurrent", variable_update="positive", node_model="ElectronGeneration")
    CreateNodeModel(dev, reg, "PCharge", "ElectronCharge * Holes")
    CreateNodeModelDerivative(dev, reg, "PCharge", "ElectronCharge * Holes", "Holes")
    ds.equation(device=dev, region=reg, name=hce_name, variable_name="Holes", time_node_model="PCharge",
                edge_model="HoleCurrent", variable_update="positive", node_model="HoleGeneration")
    for c in ("top", "bot"):
        CreateSiliconDriftDiffusionAtContact(dev, reg, c)
    ds.solve(type="dc", absolute_error=1e10, relative_error=1e-12, maximum_iterations=50)

    results = []
    v_now = 0.0
    for vb in biases:
        # ramp in 0.05 V steps
        while abs(v_now - vb) > 1e-12:
            step = max(-0.05, min(0.05, vb - v_now))
            v_now += step
            ds.set_parameter(device=dev, name="top_bias", value=v_now)
            ds.solve(type="dc", absolute_error=1e10, relative_error=1e-12, maximum_iterations=50)
        # polish
        ds.solve(type="dc", absolute_error=1e10, relative_error=1e-14, maximum_iterations=10)
        psi = list(ds.get_node_model_values(device=dev, region=reg, name="Potential"))
        n = list(ds.get_node_model_values(device=dev, region=reg, name="Electrons"))
        p = list(ds.get_node_model_values(device=dev, region=reg, name="Holes"))
        jn = list(ds.get_edge_model_values(device=dev, region=reg, name="ElectronCurrent"))
        jp = list(ds.get_edge_model_values(device=dev, region=reg, name="HoleCurrent"))
        ie = ds.get_contact_current(device=dev, contact="top", equation=ece_name)
        ih = ds.get_contact_current(device=dev, contact="top", equation=hce_name)
        ibe = ds.get_contact_current(device=dev, contact="bot", equation=ece_name)
        ibh = ds.get_contact_current(device=dev, contact="bot", equation=hce_name)
        results.append(dict(bias=vb, psi=psi, n=n, p=p, jn=jn, jp=jp, j_top=ie + ih, j_bot=ibe + ibh,
                            j_edge=[a + b for a, b in zip(jn, jp)]))
    return net, tot, results


# ---------------------------------------------------------------------------------------------
# Exact residuals (a mirror of the checker's arithmetic, for choosing the tolerance)
# ---------------------------------------------------------------------------------------------
def bern(x):
    x = mp.mpf(x)
    if abs(x) < mp.mpf("1e-30"):
        return mp.mpf(1)
    return x / mp.expm1(x)


def mu_of(ct, r):
    return mp.mpf(ct["muMin"]) + (mp.mpf(ct["muMax"]) - mp.mpf(ct["muMin"])) / (1 + r)


def residual_report(xs, net, rN, rP, res, ni):
    """max |F|/S over interior nodes for the three equations, with 50-digit arithmetic on the decimal values."""
    M = len(xs)
    psi = [mp.mpf(repr(v)) for v in res["psi"]]
    n = [mp.mpf(repr(v)) for v in res["n"]]
    p = [mp.mpf(repr(v)) for v in res["p"]]
    x = [mp.mpf(repr(v)) for v in xs]
    tauN, tauP = mp.mpf(TAU_N), mp.mpf(TAU_P)
    muN = [mu_of(CT_N, r) for r in rN]
    muP = [mu_of(CT_P, r) for r in rP]
    worst = dict(psi=mp.mpf(0), n=mp.mpf(0), p=mp.mpf(0))
    Jtot = []
    S_budget = mp.mpf(0)
    for e in range(M - 1):
        h = x[e + 1] - x[e]
        d = (psi[e] - psi[e + 1]) / VT
        B = bern(d)
        Bn = B + d
        cN = q * (muN[e] + muN[e + 1]) / 2 * VT / h
        cP = q * (muP[e] + muP[e + 1]) / 2 * VT / h
        Jn = cN * (n[e + 1] * Bn - n[e] * B)
        Jp = -cP * (p[e + 1] * B - p[e] * Bn)
        Jtot.append((Jn, Jp, cN * (n[e + 1] * abs(Bn) + n[e] * abs(B)), cP * (p[e + 1] * abs(B) + p[e] * abs(Bn))))
    for i in range(1, M - 1):
        hm, hp_ = x[i] - x[i - 1], x[i + 1] - x[i]
        V = (hm + hp_) / 2
        D1 = EPS * (psi[i] - psi[i + 1]) / hp_
        D0 = EPS * (psi[i - 1] - psi[i]) / hm
        rho = q * (p[i] - n[i] + net[i]) * V
        Fpsi = (D1 - D0) - rho
        Spsi = abs(D1) + abs(D0) + abs(q * V) * (abs(p[i]) + abs(n[i]) + abs(net[i]))
        U = (n[i] * p[i] - ni * ni) / (tauP * (n[i] + ni) + tauN * (p[i] + ni))
        Fn = (Jtot[i][0] - Jtot[i - 1][0]) - q * U * V
        Fp = (Jtot[i][1] - Jtot[i - 1][1]) + q * U * V
        Sn = Jtot[i][2] + Jtot[i - 1][2] + abs(q * U * V)
        Sp = Jtot[i][3] + Jtot[i - 1][3] + abs(q * U * V)
        worst["psi"] = max(worst["psi"], abs(Fpsi) / Spsi)
        worst["n"] = max(worst["n"], abs(Fn) / Sn)
        worst["p"] = max(worst["p"], abs(Fp) / Sp)
        S_budget += Sn + Sp
    j0 = Jtot[0][0] + Jtot[0][1]
    return worst, j0, S_budget, Jtot[0][2] + Jtot[0][3]


# ---------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__), "..", "certs"))
    ap.add_argument("--pwell-dose", default="1.3e13")
    ap.add_argument("--nplus-dose", default="1.0e15")
    ap.add_argument("--tag", default="a")
    ap.add_argument("--biases", default="-0.3,-0.5,-0.6,-0.7,1.0", help="at the top (n+) contact: negative is forward")
    ap.add_argument("--area", default="1e-6", help="cm^2 (10 um x 10 um)")
    ap.add_argument("--depth", default="1.0e-4", help="cm")
    ap.add_argument("--tol", default="1e-12")
    ap.add_argument("--mob-delta", default="1e-9")
    ap.add_argument("--dg-tol", default="1e-12")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    background = "-8.0e14"  # p-type substrate, sky130 Table 3a background concentration
    steps = sky130_recipe(args.pwell_dose, args.nplus_dose)
    w, recipe, certs = run_recipe(steps, background)
    depth = float(args.depth)
    xj = find_junction(w, depth)
    xs = mesh_points(depth)
    print(f"[{args.tag}] junction at {xj*1e7:.1f} nm, {len(xs)} nodes, films {[(m, dec(t, 6)) for m, t in w.films]}, "
          f"removed {dec(w.removed, 6)} cm, ni {dec(NI, 8)}", file=sys.stderr)
    for g in w.dopants:
        print(f"   {g['species']}: dose {dec(g['dose'],4)} rp {dec(g['rp']*1e7,5)} nm sigma {dec(mp.sqrt(g['var'])*1e7,5)} nm",
              file=sys.stderr)
    area = float(args.area)
    biases = [float(b) for b in args.biases.split(",")]
    net, tot, results = solve_device(w, xs, biases, area, args.tag)

    # mobility bracket witnesses r = (Ntot/Nref)^alpha, 50 digits
    rN = [(t / mp.mpf(CT_N["nRef"])) ** (mp.mpf(CT_N["alphaNum"]) / CT_N["alphaDen"]) for t in tot]
    rP = [(t / mp.mpf(CT_P["nRef"])) ** (mp.mpf(CT_P["alphaNum"]) / CT_P["alphaDen"]) for t in tot]

    spec_common = dict(si=SI, ctN=CT_N, ctP=CT_P, tauN=TAU_N, tauP=TAU_P, background=background, recipe=recipe,
                       xCm=[repr(x) for x in xs], areaCm2=args.area, tolRel=args.tol, mobDelta=args.mob_delta,
                       dealGroveTol=args.dg_tol)
    iv = []
    for res in results:
        vb = res["bias"]
        worst, j0, s_budget, s_j0 = residual_report(xs, net, rN, rP, res, NI)
        i_top = res["j_top"] * area
        print(f"[{args.tag}] V={vb:.2f} I_top={i_top:.6e} A (J_top {res['j_top']:.6e}, J_bot {res['j_bot']:.6e}, "
              f"J_edge0 {res['j_edge'][0]:.6e}, mid {res['j_edge'][len(xs)//2]:.6e}) "
              f"worst |F|/S psi {mp.nstr(worst['psi'],3)} n {mp.nstr(worst['n'],3)} p {mp.nstr(worst['p'],3)}; "
              f"|j0(exact)-J_top| {mp.nstr(abs(j0 - mp.mpf(repr(res['j_top']))),3)}; "
              f"tol*S_budget {mp.nstr(mp.mpf(args.tol)*s_budget,3)} A/cm2, tol*S_J0 {mp.nstr(mp.mpf(args.tol)*s_j0,3)}",
              file=sys.stderr)
        spec = dict(spec_common, biasV=repr(vb))
        cert = dict(recipeCert=certs, ni=dec(NI), doping=[dec(v) for v in net], total=[dec(v) for v in tot],
                    psi=[repr(v) for v in res["psi"]], n=[repr(v) for v in res["n"]], p=[repr(v) for v in res["p"]],
                    rN=[dec(v, 40) for v in rN], rP=[dec(v, 40) for v in rP], currentA=repr(i_top))
        name = f"{args.tag}_{vb:.2f}".replace("-", "m")
        with open(os.path.join(args.out, f"spec_{name}.json"), "w") as f:
            dump_numbers(spec, f)
        with open(os.path.join(args.out, f"cert_{name}.json"), "w") as f:
            dump_numbers(cert, f)
        iv.append(dict(biasV=vb, currentA=i_top, jTop=res["j_top"], jBot=res["j_bot"],
                       worstPsi=float(worst["psi"]), worstN=float(worst["n"]), worstP=float(worst["p"]),
                       tolBudgetAPerCm2=float(mp.mpf(args.tol) * s_budget)))
    with open(os.path.join(args.out, f"iv_{args.tag}.json"), "w") as f:
        json.dump(dict(tag=args.tag, pwellDose=args.pwell_dose, nplusDose=args.nplus_dose, junctionCm=xj, nodes=len(xs),
                       iv=iv), f, indent=1)


if __name__ == "__main__":
    main()
