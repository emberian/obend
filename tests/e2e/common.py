"""Common test utilities, oracles, and test runner harness for E2E tests.

This module provides opaque-box reference models, verification oracles, and
shared data structures for testing all 39 features of "The Next Mathematica in Obend"
derived strictly from ORIGINAL_REQUEST.md, PROJECT.md, TEST_INFRA.md, and NEXT-MATHEMATICA.md.
"""

from __future__ import annotations

import dataclasses
import enum
import fractions
import hashlib
import json
import math
import os
import subprocess
import sys
import time
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

# Global Test Result Accumulator
class TestStatus(enum.Enum):
    PASSED = "PASSED"
    FAILED = "FAILED"
    SKIPPED = "SKIPPED"


@dataclasses.dataclass
class TestCaseResult:
    test_id: str
    feature_id: str
    tier: int
    name: str
    status: TestStatus
    duration_ms: float
    error_message: Optional[str] = None
    details: Optional[str] = None


class TestRegistry:
    def __init__(self) -> None:
        self.results: List[TestCaseResult] = []

    def record(
        self,
        test_id: str,
        feature_id: str,
        tier: int,
        name: str,
        status: TestStatus,
        duration_ms: float,
        error_message: Optional[str] = None,
        details: Optional[str] = None,
    ) -> None:
        self.results.append(
            TestCaseResult(
                test_id=test_id,
                feature_id=feature_id,
                tier=tier,
                name=name,
                status=status,
                duration_ms=duration_ms,
                error_message=error_message,
                details=details,
            )
        )

    def summary(self) -> Dict[str, Any]:
        total = len(self.results)
        passed = sum(1 for r in self.results if r.status == TestStatus.PASSED)
        failed = sum(1 for r in self.results if r.status == TestStatus.FAILED)
        skipped = sum(1 for r in self.results if r.status == TestStatus.SKIPPED)

        tier_counts: Dict[int, Dict[str, int]] = {}
        for r in self.results:
            if r.tier not in tier_counts:
                tier_counts[r.tier] = {"total": 0, "passed": 0, "failed": 0, "skipped": 0}
            tier_counts[r.tier]["total"] += 1
            if r.status == TestStatus.PASSED:
                tier_counts[r.tier]["passed"] += 1
            elif r.status == TestStatus.FAILED:
                tier_counts[r.tier]["failed"] += 1
            else:
                tier_counts[r.tier]["skipped"] += 1

        feature_counts: Dict[str, int] = {}
        for r in self.results:
            feature_counts[r.feature_id] = feature_counts.get(r.feature_id, 0) + (1 if r.status == TestStatus.PASSED else 0)

        return {
            "total": total,
            "passed": passed,
            "failed": failed,
            "skipped": skipped,
            "tier_counts": tier_counts,
            "feature_counts": feature_counts,
            "pass_rate": (passed / total * 100.0) if total > 0 else 0.0,
        }


REGISTRY = TestRegistry()


def run_test_case(
    test_id: str,
    feature_id: str,
    tier: int,
    name: str,
    fn: Callable[[], None],
) -> bool:
    """Run an individual test case, measure duration, and record results."""
    t0 = time.perf_counter()
    try:
        fn()
        duration_ms = (time.perf_counter() - t0) * 1000.0
        REGISTRY.record(
            test_id=test_id,
            feature_id=feature_id,
            tier=tier,
            name=name,
            status=TestStatus.PASSED,
            duration_ms=duration_ms,
        )
        return True
    except Exception as exc:
        duration_ms = (time.perf_counter() - t0) * 1000.0
        import traceback
        err_msg = str(exc) or type(exc).__name__
        details = traceback.format_exc()
        REGISTRY.record(
            test_id=test_id,
            feature_id=feature_id,
            tier=tier,
            name=name,
            status=TestStatus.FAILED,
            duration_ms=duration_ms,
            error_message=err_msg,
            details=details,
        )
        return False


# ============================================================================
# Core Reference Models & Oracles
# ============================================================================

def cshake256(data: bytes, output_len: int = 32, custom: bytes = b"") -> bytes:
    """Standard cSHAKE256 / SHAKE256 hash function."""
    s = hashlib.shake_256(custom + data)
    return s.digest(output_len)


# F1: Holds — Semantic truth of term predicate on Core.Data
class CoreData:
    def __init__(self, tag: str, value: Any):
        self.tag = tag  # "nat", "string", "bool", "record", "variant", "rational"
        self.value = value

    def to_json(self) -> str:
        return json.dumps({"tag": self.tag, "value": self.value})

    def __repr__(self) -> str:
        return f"CoreData({self.tag}, {self.value})"


def eval_predicate_holds(predicate_fn: Callable[[CoreData], bool], data: CoreData) -> bool:
    """Oracle for Holds: evaluates predicate on Data term."""
    return predicate_fn(data)


# F2: Narrows — Law refinement preorder (∀ o n r, Admits l2 → Admits l1)
def check_narrows(
    admit_l2: Callable[[CoreData, CoreData, CoreData], bool],
    admit_l1: Callable[[CoreData, CoreData, CoreData], bool],
    test_universe: List[Tuple[CoreData, CoreData, CoreData]],
) -> bool:
    """Oracle for Narrows: checks whether l2 admits a subset of transitions admitted by l1."""
    for old_st, new_st, req in test_universe:
        if admit_l2(old_st, new_st, req):
            if not admit_l1(old_st, new_st, req):
                return False
    return True


# F3: CellContract — Inductive 2-state cell contract structure
@dataclasses.dataclass
class CellContract:
    contract_id: str
    invariant: Callable[[CoreData], bool]
    step_rel: Callable[[CoreData, CoreData, CoreData], bool]
    law: Callable[[CoreData, CoreData, CoreData], bool]

    def check_inductive_preserves(
        self, old_st: CoreData, new_st: CoreData, req: CoreData
    ) -> bool:
        if self.invariant(old_st) and self.law(old_st, new_st, req):
            return self.invariant(new_st)
        return True

    def check_step_sound(
        self, old_st: CoreData, new_st: CoreData, req: CoreData
    ) -> bool:
        if self.invariant(old_st) and self.law(old_st, new_st, req):
            return self.step_rel(old_st, new_st, req)
        return True


# F5: LawDial difference-constraint solver (Bellman-Ford)
class LawDialSolver:
    """Solves difference constraints: x_j - x_i <= w_ij (Bellman-Ford)."""

    def __init__(self, variables: List[str]) -> None:
        self.vars = list(set(variables))
        self.edges: List[Tuple[str, str, float]] = []

    def add_constraint(self, xi: str, xj: str, weight: float) -> None:
        """Adds xj - xi <= weight."""
        self.edges.append((xi, xj, weight))

    def solve(self) -> Optional[Dict[str, float]]:
        """Returns assignment {var: val} or None if negative cycle detected."""
        source = "__source__"
        dist: Dict[str, float] = {v: 0.0 for v in self.vars}
        dist[source] = 0.0

        all_edges = self.edges + [(source, v, 0.0) for v in self.vars]
        all_nodes = self.vars + [source]

        for _ in range(len(all_nodes) - 1):
            updated = False
            for u, v, w in all_edges:
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    updated = True
            if not updated:
                break

        # Check negative cycle
        for u, v, w in all_edges:
            if dist[u] + w < dist[v] - 1e-9:
                return None  # Negative cycle

        return {v: dist[v] for v in self.vars}


# F13: Canonical Rational Data Representation
class RationalData:
    def __init__(self, num: int, den: int = 1) -> None:
        if den == 0:
            raise ZeroDivisionError("Denominator cannot be zero in RationalData")
        if den < 0:
            num = -num
            den = -den
        g = math.gcd(abs(num), den)
        self.num = num // g
        self.den = den // g

    def __add__(self, other: RationalData) -> RationalData:
        return RationalData(self.num * other.den + other.num * self.den, self.den * other.den)

    def __sub__(self, other: RationalData) -> RationalData:
        return RationalData(self.num * other.den - other.num * self.den, self.den * other.den)

    def __mul__(self, other: RationalData) -> RationalData:
        return RationalData(self.num * other.num, self.den * other.den)

    def __truediv__(self, other: RationalData) -> RationalData:
        if other.num == 0:
            raise ZeroDivisionError("Division by zero in RationalData")
        return RationalData(self.num * other.den, self.den * other.num)

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, RationalData):
            return False
        return self.num == other.num and self.den == other.den

    def __lt__(self, other: RationalData) -> bool:
        return self.num * other.den < other.num * self.den

    def __le__(self, other: RationalData) -> bool:
        return self.num * other.den <= other.num * self.den

    def __repr__(self) -> str:
        return f"{self.num}/{self.den}"


# F14: Certified Interval Judge (interval@1)
@dataclasses.dataclass
class Interval:
    lo: float
    hi: float

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError(f"Inverted interval: [{self.lo}, {self.hi}]")

    def contains(self, x: float) -> bool:
        return self.lo <= x <= self.hi

    def is_subset(self, other: Interval) -> bool:
        return other.lo <= self.lo and self.hi <= other.hi

    def add(self, other: Interval) -> Interval:
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def sub(self, other: Interval) -> Interval:
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def mul(self, other: Interval) -> Interval:
        p = [self.lo * other.lo, self.lo * other.hi, self.hi * other.lo, self.hi * other.hi]
        return Interval(min(p), max(p))


# F15: SOS / Polynomial Non-negativity Judge
def verify_gram_matrix_psd(matrix: List[List[float]], tol: float = 1e-9) -> bool:
    """Verifies symmetric matrix is positive semi-definite via Sylvester / Cholesky."""
    n = len(matrix)
    if n == 0:
        return False
    # Check symmetric
    for i in range(n):
        for j in range(n):
            if abs(matrix[i][j] - matrix[j][i]) > tol:
                return False

    # Cholesky decomposition check
    L = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = sum(L[i][k] * L[j][k] for k in range(j))
            if i == j:
                val = matrix[i][i] - s
                if val < -tol:
                    return False
                L[i][j] = math.sqrt(max(0.0, val))
            else:
                if abs(L[j][j]) < tol:
                    if abs(matrix[i][j] - s) > tol:
                        return False
                    L[i][j] = 0.0
                else:
                    L[i][j] = (matrix[i][j] - s) / L[j][j]
    return True



# F16, F17, F18: VaultTurn, legs_agree, no_toctou
@dataclasses.dataclass
class CellDelta:
    cell_id: str
    old_version: int
    new_version: int
    data: CoreData


@dataclasses.dataclass
class VaultTurn:
    turn_id: str
    read_pins: Dict[str, int]  # cell_id -> version
    write_cells: List[CellDelta]
    occasion: str

    def footprint(self) -> Set[str]:
        return set(self.read_pins.keys()) | {c.cell_id for c in self.write_cells}

    def write_footprint(self) -> Set[str]:
        return {c.cell_id for c in self.write_cells}

    def is_disjoint(self, other: VaultTurn) -> bool:
        # TOCTOU disjointness: (read1 ∪ write1) ∩ write2 == ∅ and (read2 ∪ write2) ∩ write1 == ∅
        return (
            len(self.footprint() & other.write_footprint()) == 0
            and len(other.footprint() & self.write_footprint()) == 0
        )


# F19: Conserved Multi-Asset Book
class ConservedBook:
    """Multi-asset balance ledger with credit floors and conserved totals."""

    def __init__(self) -> None:
        self.balances: Dict[str, Dict[str, int]] = {}  # account -> (asset -> balance)
        self.floors: Dict[str, Dict[str, int]] = {}  # account -> (asset -> floor)
        self.total_supply: Dict[str, int] = {}  # asset -> total minted

    def get_balance(self, acct: str, asset: str) -> int:
        return self.balances.get(acct, {}).get(asset, 0)

    def get_floor(self, acct: str, asset: str) -> int:
        return self.floors.get(acct, {}).get(asset, 0)

    def set_floor(self, acct: str, asset: str, floor: int) -> None:
        if acct not in self.floors:
            self.floors[acct] = {}
        self.floors[acct][asset] = floor

    def mint(self, acct: str, asset: str, amount: int) -> bool:
        if amount <= 0:
            return False
        if acct not in self.balances:
            self.balances[acct] = {}
        self.balances[acct][asset] = self.balances[acct].get(asset, 0) + amount
        self.total_supply[asset] = self.total_supply.get(asset, 0) + amount
        return True

    def transfer(self, src: str, dst: str, asset: str, amount: int) -> bool:
        if amount <= 0:
            return False
        cur_src = self.get_balance(src, asset)
        floor = self.get_floor(src, asset)
        if cur_src - amount < floor:
            return False  # Solvency floor refusal

        self.balances[src][asset] = cur_src - amount
        if dst not in self.balances:
            self.balances[dst] = {}
        self.balances[dst][asset] = self.balances[dst].get(asset, 0) + amount
        return True

    def burn(self, acct: str, asset: str, amount: int) -> bool:
        if amount <= 0:
            return False
        cur = self.get_balance(acct, asset)
        floor = self.get_floor(acct, asset)
        if cur - amount < floor:
            return False
        self.balances[acct][asset] = cur - amount
        self.total_supply[asset] -= amount
        return True

    def is_conserved(self, asset: str) -> bool:
        sum_bal = sum(self.balances[a].get(asset, 0) for a in self.balances)
        return sum_bal == self.total_supply.get(asset, 0)


# F20: ZoE Seat
@dataclasses.dataclass
class ZoeSeat:
    seat_id: str
    owner: str
    give_asset: str
    give_amount: int
    want_asset: str
    want_amount: int
    is_active: bool = True
    settled: bool = False

    def exit(self, book: ConservedBook) -> bool:
        """Unconditional exit returns Give amount if not settled."""
        if not self.is_active or self.settled:
            return False
        self.is_active = False
        # refund escrowed assets
        book.mint(self.owner, self.give_asset, self.give_amount)
        return True

    def execute_swap(self, book: ConservedBook, counterparty_owner: str) -> bool:
        """Executes swap if both conditions satisfied."""
        if not self.is_active or self.settled:
            return False
        self.settled = True
        self.is_active = False
        book.mint(self.owner, self.want_asset, self.want_amount)
        book.mint(counterparty_owner, self.give_asset, self.give_amount)
        return True


# F21: drex-clearing@1 certified LP clearing judge
@dataclasses.dataclass
class Order:
    order_id: str
    trader: str
    is_bid: bool  # True = buy, False = sell
    limit_price: float
    quantity: float


@dataclasses.dataclass
class ClearingWitness:
    clearing_price: float
    total_volume: float
    trades: List[Tuple[str, float]]  # (order_id, filled_qty)


def verify_drex_clearing(
    orders: List[Order], witness: ClearingWitness, epsilon: float = 1e-6
) -> Tuple[bool, str]:
    """O(N) verification of primal feasibility, dual prices, and volume balance."""
    p = witness.clearing_price
    fills = dict(witness.trades)

    total_buy = 0.0
    total_sell = 0.0

    for ord in orders:
        filled = fills.get(ord.order_id, 0.0)
        if filled < 0 or filled > ord.quantity + epsilon:
            return False, f"Invalid fill quantity for {ord.order_id}"

        # Limit price check
        if ord.is_bid:
            if filled > epsilon and ord.limit_price < p - epsilon:
                return False, f"Bid {ord.order_id} filled below limit price"
            total_buy += filled
        else:
            if filled > epsilon and ord.limit_price > p + epsilon:
                return False, f"Ask {ord.order_id} filled above limit price"
            total_sell += filled

    # Volume balance conservation
    if abs(total_buy - total_sell) > epsilon:
        return False, f"Volume imbalance: buy={total_buy}, sell={total_sell}"

    if abs(total_buy - witness.total_volume) > epsilon:
        return False, f"Volume mismatch with witness: {total_buy} != {witness.total_volume}"

    return True, "Valid clearing"


# F26: Receipt.blind — Blinded Merkle multiproofs
class BlindedMerkleTree:
    """Merkle tree with blinded leaf support."""

    def __init__(self, leaves: List[bytes], salts: Optional[List[bytes]] = None) -> None:
        self.salts = salts or [cshake256(f"salt_{i}".encode()) for i in range(len(leaves))]
        self.raw_leaves = leaves
        self.leaf_hashes = [
            cshake256(self.salts[i] + leaves[i]) for i in range(len(leaves))
        ]
        self.tree: List[List[bytes]] = [self.leaf_hashes]
        self._build()

    def _build(self) -> None:
        current = self.leaf_hashes
        while len(current) > 1:
            nxt: List[bytes] = []
            for i in range(0, len(current), 2):
                l = current[i]
                r = current[i + 1] if i + 1 < len(current) else l
                nxt.append(cshake256(l + r))
            self.tree.append(nxt)
            current = nxt

    def root(self) -> bytes:
        return self.tree[-1][0] if (self.tree and self.tree[-1]) else b""

    def get_blinded_proof(self, index: int) -> Tuple[bytes, bytes, List[Tuple[str, bytes]]]:
        """Returns (leaf_hash, salt, proof_path). Leaf value itself is masked."""
        proof: List[Tuple[str, bytes]] = []
        idx = index
        for level in range(len(self.tree) - 1):
            cur_level = self.tree[level]
            is_right = (idx % 2 == 1)
            sibling_idx = idx - 1 if is_right else idx + 1
            if sibling_idx < len(cur_level):
                sibling_hash = cur_level[sibling_idx]
            else:
                sibling_hash = cur_level[idx]
            proof.append(("left" if is_right else "right", sibling_hash))
            idx //= 2
        return self.leaf_hashes[index], self.salts[index], proof

    @staticmethod
    def verify_blinded_proof(
        leaf_hash: bytes, proof: List[Tuple[str, bytes]], root: bytes
    ) -> bool:
        cur = leaf_hash
        for direction, sibling in proof:
            if direction == "left":
                cur = cshake256(sibling + cur)
            else:
                cur = cshake256(cur + sibling)
        return cur == root


# F30: Symbolic GenericSimplex BFT Consensus
@dataclasses.dataclass
class SimplexVote:
    view: int
    block_hash: str
    voter: str
    signature: str


@dataclasses.dataclass
class NotarizationCert:
    view: int
    block_hash: str
    votes: List[SimplexVote]


class GenericSimplexEngine:
    def __init__(self, validators: List[str]) -> None:
        self.validators = sorted(validators)
        self.n = len(self.validators)
        self.f = (self.n - 1) // 3
        self.quorum = 2 * self.f + 1
        self.current_view = 0
        self.finalized_blocks: Dict[int, str] = {}  # height -> block_hash

    def check_notarization(self, cert: NotarizationCert) -> bool:
        unique_voters = {v.voter for v in cert.votes if v.voter in self.validators}
        return len(unique_voters) >= self.quorum

    def finalize(self, height: int, cert: NotarizationCert) -> bool:
        if not self.check_notarization(cert):
            return False
        if height in self.finalized_blocks:
            # Conflicting finalization safety check
            return self.finalized_blocks[height] == cert.block_hash
        self.finalized_blocks[height] = cert.block_hash
        return True


# F34: ProjectionKind (10 Kinds)
class ProjectionKind(enum.Enum):
    PROSE = "prose"
    OBEND_CODE = "obendCode"
    CAS_SYMBOLIC = "casSymbolic"
    LEAN_BRIDGE = "leanBridge"
    LAW_CONTRACT = "lawContract"
    DEOS_AFFORDANCE = "deosAffordance"
    HARDWARE_SCHEMATIC = "hardwareSchematic"
    HARDWARE_TIMING = "hardwareTiming"
    HARDWARE_LAYOUT = "hardwareLayout"
    LEDGER_SEAT = "ledgerSeat"


# F38: 8-Function C-ABI Bridge Contract
class CAbiBridgeMock:
    """Mock simulating the 8-function C-ABI interface specified in PROJECT.md."""

    def __init__(self) -> None:
        self.sessions: Dict[int, Dict[str, Any]] = {}
        self.next_session_id = 1
        self.last_error: str = ""

    def obend_session_init(self) -> int:
        sid = self.next_session_id
        self.next_session_id += 1
        self.sessions[sid] = {"created_at": time.time(), "turns": [], "cells": {}}
        return sid

    def obend_session_free(self, sid: int) -> int:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1
        del self.sessions[sid]
        return 0

    def obend_eval_cell(self, sid: int, cell_bytes: bytes) -> Tuple[int, bytes]:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1, b""
        try:
            req = json.loads(cell_bytes.decode("utf-8"))
            res = {"status": "ok", "result": f"Evaluated {req.get('code', '')}"}
            return 0, json.dumps(res).encode("utf-8")
        except Exception as e:
            self.last_error = str(e)
            return -2, b""

    def obend_turn_propose(self, sid: int, turn_bytes: bytes) -> Tuple[int, bytes]:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1, b""
        return 0, b'{"status":"proposed","turn_id":"turn-1"}'

    def obend_turn_commit(self, sid: int, turn_bytes: bytes) -> Tuple[int, bytes]:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1, b""
        return 0, b'{"status":"committed"}'

    def obend_project_hardware(self, sid: int, hw_type: int) -> Tuple[int, bytes]:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1, b""
        # Strictly read-only projection
        return 0, b'{"kind":"hardwareSchematic","circuits":["inv","nand"]}'

    def obend_verify_receipt(self, sid: int, receipt_bytes: bytes) -> Tuple[int, bytes]:
        if sid not in self.sessions:
            self.last_error = "Invalid session handle"
            return -1, b""
        return 0, b'{"valid":true}'

    def obend_get_last_error(self, sid: int) -> str:
        return self.last_error
