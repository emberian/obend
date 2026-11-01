#!/usr/bin/env python3
"""Milestone 6 Phase 2: Tier 5 Adversarial Coverage Audit Harness.

Adversarial stress-testing of all reference models, consensus invariants,
clearing judges, Merkle multiproofs, and ledger safety mechanisms.
"""

from __future__ import annotations

import math
import os
import sys
import unittest

# Ensure tests/e2e is on path
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(REPO_ROOT, "tests", "e2e"))

from common import (
    BlindedMerkleTree,
    ConservedBook,
    CoreData,
    GenericSimplexEngine,
    Interval,
    LawDialSolver,
    NotarizationCert,
    Order,
    ClearingWitness,
    SimplexVote,
    VaultTurn,
    CellDelta,
    ZoeSeat,
    cshake256,
    verify_drex_clearing,
    verify_gram_matrix_psd,
)


class Tier5AdversarialAudit(unittest.TestCase):
    def test_01_law_dial_negative_cycles(self):
        """Stress-test LawDial difference-constraint solver on negative cycles & dense graphs."""
        # Simple negative cycle: x1 - x0 <= 2, x0 - x1 <= -3 => 0 <= -1 (infeasible)
        solver = LawDialSolver(["x0", "x1"])
        solver.add_constraint("x0", "x1", 2.0)
        solver.add_constraint("x1", "x0", -3.0)
        self.assertIsNone(solver.solve(), "Negative 2-cycle must be detected as infeasible")

        # Infeasible 5-cycle: x_i - x_{i-1} <= 1, x_0 - x_4 <= -6
        nodes = [f"v{i}" for i in range(5)]
        solver5 = LawDialSolver(nodes)
        for i in range(4):
            solver5.add_constraint(nodes[i], nodes[i + 1], 1.0)
        solver5.add_constraint(nodes[4], nodes[0], -6.0)
        self.assertIsNone(solver5.solve(), "Negative 5-cycle must be detected as infeasible")

        # Feasible dense difference constraint graph with 20 nodes
        dense_nodes = [f"d{i}" for i in range(20)]
        dense_solver = LawDialSolver(dense_nodes)
        for i in range(19):
            dense_solver.add_constraint(dense_nodes[i], dense_nodes[i + 1], 2.5)
            dense_solver.add_constraint(dense_nodes[i + 1], dense_nodes[i], 1.0)
        sol = dense_solver.solve()
        self.assertIsNotNone(sol, "Feasible system must have a valid solution")
        for i in range(19):
            u, v = dense_nodes[i], dense_nodes[i + 1]
            self.assertLessEqual(sol[v] - sol[u], 2.5 + 1e-7)
            self.assertLessEqual(sol[u] - sol[v], 1.0 + 1e-7)

    def test_02_drex_clearing_adversarial_exploits(self):
        """Stress-test drex-clearing@1 certified LP judge under adversarial market conditions."""
        orders = [
            Order("b1", "trader_a", True, 100.0, 10.0),   # Bid: max 100
            Order("s1", "trader_b", False, 90.0, 10.0),   # Ask: min 90
        ]

        # Valid baseline clearing at price 95, volume 10
        valid_witness = ClearingWitness(95.0, 10.0, [("b1", 10.0), ("s1", 10.0)])
        ok, msg = verify_drex_clearing(orders, valid_witness)
        self.assertTrue(ok, f"Valid clearing failed: {msg}")

        # Attack 1: Fill above bid limit price
        bad_price_witness = ClearingWitness(105.0, 10.0, [("b1", 10.0), ("s1", 10.0)])
        ok, _ = verify_drex_clearing(orders, bad_price_witness)
        self.assertFalse(ok, "Filling bid above limit price must be rejected")

        # Attack 2: Fill below ask limit price
        bad_ask_witness = ClearingWitness(85.0, 10.0, [("b1", 10.0), ("s1", 10.0)])
        ok, _ = verify_drex_clearing(orders, bad_ask_witness)
        self.assertFalse(ok, "Filling ask below limit price must be rejected")

        # Attack 3: Over-allocation (fill > quantity)
        overfill_witness = ClearingWitness(95.0, 12.0, [("b1", 12.0), ("s1", 12.0)])
        ok, _ = verify_drex_clearing(orders, overfill_witness)
        self.assertFalse(ok, "Overfill beyond order quantity must be rejected")

        # Attack 4: Volume imbalance (buy != sell)
        imbalance_witness = ClearingWitness(95.0, 10.0, [("b1", 10.0), ("s1", 8.0)])
        ok, _ = verify_drex_clearing(orders, imbalance_witness)
        self.assertFalse(ok, "Volume conservation imbalance must be rejected")

        # Attack 5: Negative fill quantity
        neg_fill_witness = ClearingWitness(95.0, 0.0, [("b1", -5.0), ("s1", -5.0)])
        ok, _ = verify_drex_clearing(orders, neg_fill_witness)
        self.assertFalse(ok, "Negative fill must be rejected")

    def test_03_blinded_merkle_tree_adversarial(self):
        """Stress-test Blinded Merkle multiproofs against tampering, forgery, and privacy leaks."""
        leaves = [f"confidential_cell_{i}".encode("utf-8") for i in range(16)]
        tree = BlindedMerkleTree(leaves)
        root = tree.root()
        self.assertEqual(len(root), 32)

        # Valid blinded proof verification for all leaves
        for idx in range(16):
            leaf_hash, salt, proof = tree.get_blinded_proof(idx)
            # Reconstruct masked leaf
            self.assertEqual(leaf_hash, cshake256(salt + leaves[idx]))
            # Stranger verification without raw leaf
            self.assertTrue(
                BlindedMerkleTree.verify_blinded_proof(leaf_hash, proof, root),
                f"Valid blinded proof for leaf {idx} failed",
            )

        # Forgery Attack 1: Altered leaf hash
        leaf_hash, salt, proof = tree.get_blinded_proof(3)
        fake_hash = bytearray(leaf_hash)
        fake_hash[0] ^= 0xFF
        self.assertFalse(
            BlindedMerkleTree.verify_blinded_proof(bytes(fake_hash), proof, root),
            "Tampered leaf hash must fail verification",
        )

        # Forgery Attack 2: Proof path tampering
        bad_proof = list(proof)
        dir_, sib = bad_proof[0]
        fake_sib = bytearray(sib)
        fake_sib[1] ^= 0x55
        bad_proof[0] = (dir_, bytes(fake_sib))
        self.assertFalse(
            BlindedMerkleTree.verify_blinded_proof(leaf_hash, bad_proof, root),
            "Tampered proof sibling must fail verification",
        )

        # Forgery Attack 3: Proof against incorrect root
        fake_root = cshake256(b"wrong_root")
        self.assertFalse(
            BlindedMerkleTree.verify_blinded_proof(leaf_hash, proof, fake_root),
            "Proof against wrong root must fail verification",
        )

    def test_04_conserved_book_adversarial(self):
        """Stress-test multi-asset conserved book against negative values, floor underflows & leaks."""
        book = ConservedBook()
        self.assertTrue(book.mint("alice", "OBND", 1000))
        self.assertTrue(book.mint("bob", "OBND", 500))
        self.assertTrue(book.is_conserved("OBND"))

        # Attack 1: Negative transfer
        self.assertFalse(book.transfer("alice", "bob", "OBND", -100))
        self.assertEqual(book.get_balance("alice", "OBND"), 1000)

        # Attack 2: Transfer with zero amount
        self.assertFalse(book.transfer("alice", "bob", "OBND", 0))

        # Attack 3: Overdraft exceeding balance
        self.assertFalse(book.transfer("alice", "bob", "OBND", 1001))

        # Attack 4: Solvency floor violation
        book.set_floor("alice", "OBND", 300)
        # Attempt to transfer 750 (leaving 250 < floor 300)
        self.assertFalse(book.transfer("alice", "bob", "OBND", 750))
        self.assertEqual(book.get_balance("alice", "OBND"), 1000)

        # Valid transfer respecting floor: transfer 700 (leaving 300 == floor)
        self.assertTrue(book.transfer("alice", "bob", "OBND", 700))
        self.assertEqual(book.get_balance("alice", "OBND"), 300)
        self.assertEqual(book.get_balance("bob", "OBND"), 1200)
        self.assertTrue(book.is_conserved("OBND"))

        # Attack 5: Negative burn
        self.assertFalse(book.burn("bob", "OBND", -50))

        # Valid burn
        self.assertTrue(book.burn("bob", "OBND", 200))
        self.assertEqual(book.get_balance("bob", "OBND"), 1000)
        self.assertTrue(book.is_conserved("OBND"))

    def test_05_zoe_seat_adversarial(self):
        """Stress-test ZoE offer-safe seat against double-exit, race conditions, and post-swap exits."""
        book = ConservedBook()
        book.mint("alice", "USDC", 1000)
        seat = ZoeSeat("s1", "alice", "USDC", 1000, "ETH", 2)

        # Normal unconditional exit
        self.assertTrue(seat.exit(book))
        self.assertEqual(book.get_balance("alice", "USDC"), 2000)

        # Attack 1: Double exit (replay attack)
        self.assertFalse(seat.exit(book), "Second exit must be rejected")
        self.assertEqual(book.get_balance("alice", "USDC"), 2000)

        # Attack 2: Executing swap on exited seat
        self.assertFalse(seat.execute_swap(book, "counterparty"), "Swap on exited seat must fail")

        # Attack 3: Exit after settlement
        seat2 = ZoeSeat("s2", "bob", "ETH", 1, "USDC", 500)
        self.assertTrue(seat2.execute_swap(book, "alice"))
        self.assertFalse(seat2.exit(book), "Exit on settled seat must be rejected")

    def test_06_generic_simplex_adversarial(self):
        """Stress-test GenericSimplex consensus engine against equivocation & Byzantine quorums."""
        validators = ["v0", "v1", "v2", "v3"]  # N=4, f=1, quorum=3
        engine = GenericSimplexEngine(validators)
        self.assertEqual(engine.f, 1)
        self.assertEqual(engine.quorum, 3)

        # Attack 1: Sub-quorum notarization (only 2 votes, need 3)
        votes_2 = [
            SimplexVote(0, "hash_A", "v0", "sig0"),
            SimplexVote(0, "hash_A", "v1", "sig1"),
        ]
        cert_sub = NotarizationCert(0, "hash_A", votes_2)
        self.assertFalse(engine.finalize(1, cert_sub), "Sub-quorum cert must not finalize")

        # Attack 2: Duplicate votes from same voter (attempting to inflate count)
        votes_dup = [
            SimplexVote(0, "hash_A", "v0", "sig0"),
            SimplexVote(0, "hash_A", "v0", "sig0"),
            SimplexVote(0, "hash_A", "v1", "sig1"),
        ]
        cert_dup = NotarizationCert(0, "hash_A", votes_dup)
        self.assertFalse(engine.finalize(1, cert_dup), "Duplicate voter must not count toward quorum")

        # Attack 3: Imposter voter not in validator set
        votes_imposter = [
            SimplexVote(0, "hash_A", "v0", "sig0"),
            SimplexVote(0, "hash_A", "v1", "sig1"),
            SimplexVote(0, "hash_A", "attacker", "sig_att"),
        ]
        cert_imp = NotarizationCert(0, "hash_A", votes_imposter)
        self.assertFalse(engine.finalize(1, cert_imp), "Imposter voter must not count toward quorum")

        # Valid finalization at height 1
        votes_valid = [
            SimplexVote(0, "hash_A", "v0", "sig0"),
            SimplexVote(0, "hash_A", "v1", "sig1"),
            SimplexVote(0, "hash_A", "v2", "sig2"),
        ]
        cert_valid = NotarizationCert(0, "hash_A", votes_valid)
        self.assertTrue(engine.finalize(1, cert_valid))

        # Attack 4: Conflicting finalization (equivocation at same height)
        votes_conflict = [
            SimplexVote(0, "hash_B", "v1", "sig1"),
            SimplexVote(0, "hash_B", "v2", "sig2"),
            SimplexVote(0, "hash_B", "v3", "sig3"),
        ]
        cert_conflict = NotarizationCert(0, "hash_B", votes_conflict)
        self.assertFalse(engine.finalize(1, cert_conflict), "Conflicting finalization must be refused")

    def test_07_interval_and_sos_adversarial(self):
        """Stress-test numerical analysis bounds and polynomial non-negativity Gram matrices."""
        # Interval bounds
        with self.assertRaises(ValueError):
            Interval(10.0, 5.0)  # Inverted interval

        iv1 = Interval(-2.0, 3.0)
        iv2 = Interval(4.0, 6.0)
        prod = iv1.mul(iv2)
        self.assertEqual(prod.lo, -12.0)
        self.assertEqual(prod.hi, 18.0)

        # SOS Gram Matrix PSD Verification
        # Valid PSD matrix: [[2, 1], [1, 2]]
        valid_psd = [[2.0, 1.0], [1.0, 2.0]]
        self.assertTrue(verify_gram_matrix_psd(valid_psd))

        # Invalid: Non-symmetric matrix
        asym = [[2.0, 1.0], [3.0, 2.0]]
        self.assertFalse(verify_gram_matrix_psd(asym), "Asymmetric matrix is not PSD")

        # Invalid: Indefinite / Negative eigenvalue matrix [[1, 2], [2, 1]] (det = 1 - 4 = -3 < 0)
        indef = [[1.0, 2.0], [2.0, 1.0]]
        self.assertFalse(verify_gram_matrix_psd(indef), "Indefinite matrix must not pass PSD check")


if __name__ == "__main__":
    unittest.main()
