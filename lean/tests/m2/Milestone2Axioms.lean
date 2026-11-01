import Obend.Vault.Hyperedge
import Obend.Ledger.Book
import Obend.Ledger.Seat
import Obend.Judge.Clearing

open Obend.Vault
open Obend.Ledger
open Obend.Judge

#print axioms VaultTurn.legs_agree
#print axioms vaultTurn_disjoint_commutes
#print axioms no_toctou
#print axioms Operation.apply_conserves
#print axioms Batch.conservation
#print axioms weak_duality
#print axioms certifies_epsilon_optimal
