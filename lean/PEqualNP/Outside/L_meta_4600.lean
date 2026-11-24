import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4600 : have x1 : List (BitVec (59 : ℕ)) → Bool × Fin (40 : ℕ) × Fin (40 : ℕ) → List (BitVec (59 : ℕ)) := fun (x1 : List (BitVec (59 : ℕ))) (x2 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x1 ++ [if x2.1 = Bool.true then x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ)) else x1.getD ↑x2.2.1 (0 : BitVec (59 : ℕ)) &&& x1.getD ↑x2.2.2 (0 : BitVec (59 : ℕ))]; have x2 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]; ∀ (x3 : List (BitVec (59 : ℕ))) (x4 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), List.foldl x2 (List.map BitVec.toNat x3) (List.map (fun (x5 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => (x5.1, ↑x5.2.1, ↑x5.2.2)) x4) = List.map BitVec.toNat (List.foldl x1 x3 x4) := by
  intro wordStep natStep wires gates
  induction gates generalizing wires with
  | nil => rfl
  | cons gate gates ih =>
    have readWire (i : ℕ) :
        (wires.map BitVec.toNat).getD i 0 = (wires.getD i 0).toNat :=
      List.getD_map wires 0 BitVec.toNat
    have oneGate :
        natStep (wires.map BitVec.toNat) (gate.1, gate.2.1.val, gate.2.2.val) =
          (wordStep wires gate).map BitVec.toNat := by
      simp only [natStep, wordStep, readWire, List.map_append, List.map_cons, List.map_nil]
      cases gate.1 <;> simp
    simp only [List.map_cons, List.foldl_cons, oneGate]
    exact ih (wordStep wires gate)
