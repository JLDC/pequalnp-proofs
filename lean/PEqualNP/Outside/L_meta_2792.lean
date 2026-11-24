import Mathlib.Data.List.OfFn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2792

-- The wire recurrence and monotonicity proof below are from L_meta_616.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

def wire {n : ℕ} (C : Circuit) (w : ℕ) (x y : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def truthSet (n : ℕ) (C : Circuit) (w : ℕ) : Set ((Fin n → Bool) × (Fin n → Bool)) :=
  {p | wire C w p.1 p.2 = true}

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C) (w : ℕ)
    {x x' y y' : Fin n → Bool}
    (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true) :
    wire C w x y = true → wire C w x' y' = true := by
  apply wires_mono C hm
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hx j
  · simpa only [Fin.append_right] using hy j

def LeftOnly {α β : Type*} (S : Set (α × β)) : Prop :=
  ∃ A : Set α, S = A ×ˢ Set.univ

def RightOnly {α β : Type*} (S : Set (α × β)) : Prop :=
  ∃ B : Set β, S = Set.univ ×ˢ B

lemma left_of_endpoints {n : ℕ} {C : Circuit} (hm : Monotone2 C) (w : ℕ)
    (h : ∀ x : Fin n → Bool, wire C w x (fun _ => false) = wire C w x (fun _ => true)) :
    LeftOnly (truthSet n C w) := by
  refine ⟨{x | wire C w x (fun _ => false) = true}, ?_⟩
  ext ⟨x,y⟩
  change wire C w x y = true ↔ wire C w x (fun _ => false) = true ∧ True
  rw [and_true]
  constructor
  · rw [h x]
    exact pair_mono hm w (by simp) (by simp)
  · exact pair_mono hm w (by simp) (by simp)

lemma right_of_endpoints {n : ℕ} {C : Circuit} (hm : Monotone2 C) (w : ℕ)
    (h : ∀ y : Fin n → Bool, wire C w (fun _ => false) y = wire C w (fun _ => true) y) :
    RightOnly (truthSet n C w) := by
  refine ⟨{y | wire C w (fun _ => false) y = true}, ?_⟩
  ext ⟨x,y⟩
  change wire C w x y = true ↔ True ∧ wire C w (fun _ => false) y = true
  rw [true_and]
  constructor
  · rw [h y]
    exact pair_mono hm w (by simp) (by simp)
  · exact pair_mono hm w (by simp) (by simp)

lemma one_stable {α : Type*} {a b : ℕ} {f g : ℕ → α → Bool}
    (h : ¬ ∀ w ∈ [a,b], ∃ x, f w x ≠ g w x) :
    (∀ x, f a x = g a x) ∨ (∀ x, f b x = g b x) := by
  classical
  by_cases ha : ∀ x, f a x = g a x
  · exact Or.inl ha
  · right
    intro x
    by_contra hb
    exact h (by simpa using And.intro (not_forall.mp ha) (Exists.intro x hb))

-- A truth set which ignores both blocks is constant.
lemma flat_inter {α β : Type*} {S : Set (α × β)} (T : Set (α × β))
    (hl : LeftOnly S) (hr : RightOnly S) : S ∩ T = T ∨ S ∩ T = ∅ := by
  rcases hl with ⟨A, hA⟩
  rcases hr with ⟨B, hB⟩
  by_cases hs : S.Nonempty
  · obtain ⟨⟨x,y⟩, hp⟩ := hs
    rw [hB] at hp
    have hfull : S = Set.univ := by
      apply Set.eq_univ_of_forall
      rintro ⟨u,v⟩
      have huy : (u,y) ∈ S := by
        rw [hB]
        exact ⟨Set.mem_univ _, hp.2⟩
      rw [hA] at huy ⊢
      exact ⟨huy.1, Set.mem_univ _⟩
    simp [hfull]
  · simp [Set.not_nonempty_iff_eq_empty.mp hs]

def GateForm {α β : Type*} (S : ℕ → Set (α × β)) (k : ℕ) (marked : Prop) : Prop :=
  ∃ a < k, ∃ b < k,
    S k = S a ∪ S b ∨ S k = S a ∨ S k = ∅ ∨
      S k = S a ∩ S b ∧ (marked ∨ ∃ (A : Set α) (B : Set β),
        S a = A ×ˢ Set.univ ∧ S b = Set.univ ×ˢ B)

lemma unmarked_and {α β : Type*} {S : ℕ → Set (α × β)} {a b k : ℕ} {p : Prop}
    (ha : a < k) (hb : b < k) (hout : S k = S a ∩ S b)
    (hl : LeftOnly (S a) ∨ LeftOnly (S b)) (hr : RightOnly (S a) ∨ RightOnly (S b)) :
    GateForm S k p := by
  have same (i j : ℕ) (hi : i < k) (hj : j < k) (he : S k = S i ∩ S j)
      (hL : LeftOnly (S i)) (hR : RightOnly (S i)) : GateForm S k p := by
    refine ⟨j, hj, i, hi, Or.inr ?_⟩
    rcases flat_inter (S j) hL hR with h | h
    · exact Or.inl (he.trans h)
    · exact Or.inr (Or.inl (he.trans h))
  have diff (i j : ℕ) (hi : i < k) (hj : j < k) (he : S k = S i ∩ S j)
      (hL : LeftOnly (S i)) (hR : RightOnly (S j)) : GateForm S k p := by
    obtain ⟨A, hA⟩ := hL
    obtain ⟨B, hB⟩ := hR
    exact ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr ⟨he, Or.inr ⟨A, B, hA, hB⟩⟩))⟩
  have hrev : S k = S b ∩ S a := hout.trans (Set.inter_comm _ _)
  rcases hl with hla | hlb <;> rcases hr with hra | hrb
  · exact same a b ha hb hout hla hra
  · exact diff a b ha hb hout hla hrb
  · exact diff b a hb ha hrev hlb hra
  · exact same b a hb ha hrev hlb hrb

end PEqualNP.Outside.L_meta_2792

open PEqualNP.Outside.L_meta_2792

theorem PEqualNP.Outside.L_meta_2792 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  classical
  intro n C T hm hsorted hmarked
  refine ⟨truthSet n C, ?_, ?_, fun _ _ => Iff.rfl⟩
  · intro i
    constructor
    · apply Set.ext
      rintro ⟨x,y⟩
      change wire C i.val x y = true ↔ x i = true
      have he := wires_input C (Fin.append x y) i.val (by have := i.isLt; omega)
      change _ = Fin.append x y (Fin.castAdd n i) at he
      rw [wire, he, Fin.append_left]
    · apply Set.ext
      rintro ⟨x,y⟩
      change wire C (n + i.val) x y = true ↔ y i = true
      have he := wires_input C (Fin.append x y) (n + i.val) (by have := i.isLt; omega)
      change _ = Fin.append x y (Fin.natAdd n i) at he
      rw [wire, he, Fin.append_right]
  · intro j hj
    change GateForm (truthSet n C) (n + n + j) (j ∈ T)
    let g := C.gates[j]'hj
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨a,b,hin,hab,hb⟩ := hsorted j g hg
    have ha := hab.trans hb
    have he (x y : Fin n → Bool) :
        wire C (n + n + j) x y = g.op.eval [wire C a x y, wire C b x y] := by
      simpa only [wire, hin, List.map_cons, List.map_nil, ha, hb, ↓reduceIte] using
        wires_gate_ofFn C (Fin.append x y) j g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using (hm g (List.mem_of_getElem? hg)).1
    rcases hop with hand | hor
    · have hout : truthSet n C (n + n + j) = truthSet n C a ∩ truthSet n C b := by
        apply Set.ext
        rintro ⟨x,y⟩
        change wire C _ x y = true ↔ wire C a x y = true ∧ wire C b x y = true
        rw [he, hand]
        simp [GateOp.eval]
      by_cases hjT : j ∈ T
      · exact ⟨a, ha, b, hb, Or.inr (Or.inr (Or.inr ⟨hout, Or.inl hjT⟩))⟩
      · have hbad : ¬ ((∀ w ∈ [a,b], ∃ x : Fin n → Bool,
              wire C w x (fun _ => false) ≠ wire C w x (fun _ => true)) ∨
            ∀ w ∈ [a,b], ∃ y : Fin n → Bool,
              wire C w (fun _ => false) y ≠ wire C w (fun _ => true) y) := by
          simpa only [hin, wire, List.ofFn_fin_append, List.ofFn_const] using
            hmarked j g hg hand hjT
        apply unmarked_and ha hb hout
        · exact (one_stable (not_or.mp hbad).1).imp
            (left_of_endpoints hm a) (left_of_endpoints hm b)
        · exact (one_stable (not_or.mp hbad).2).imp
            (right_of_endpoints hm a) (right_of_endpoints hm b)
    · refine ⟨a, ha, b, hb, Or.inl ?_⟩
      apply Set.ext
      rintro ⟨x,y⟩
      change wire C _ x y = true ↔ wire C a x y = true ∨ wire C b x y = true
      rw [he, hor]
      simp [GateOp.eval]
