import unittest

from check_lean_vacuity import affected


class VacuityTests(unittest.TestCase):
    def test_change_to_shared_predicate_reaches_transitive_proofs(self):
        proof = "VerifiedGarbage.Proof."
        graph = {
            "Spec": [],
            "Common": ["Spec"],
            proof + "A": ["Common"],
            proof + "B": [proof + "A"],
            proof + "C": [],
        }
        self.assertEqual(list(affected(graph, {"Spec"})), [proof + "A", proof + "B"])
