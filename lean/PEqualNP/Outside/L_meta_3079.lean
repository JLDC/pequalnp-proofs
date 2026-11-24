import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_3079

-- Circuit normalization, induced-graph bounds and batched checks from PressF10, L-meta-1667.
abbrev Sig := BitVec 512

def zero : Sig := 0

def one : Sig := BitVec.allOnes 512

def neg (a : Sig) : Sig := ~~~a

def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val

lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]

lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp

lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]

lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512

def observe (a : Sig) : Wire Row := fun r => bit r a

def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]

def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a

theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _

theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]

theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he

theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)

theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]

theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)

def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d

def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig

def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2

def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row

def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩

def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)

def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r

def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)

def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a

theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)

theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w

theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)

theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)

theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)

def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1

def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1

def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1

def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)

def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one

theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)

theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat

def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))

def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)

theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0

theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)

theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 768

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1

def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)

def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h

theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h

theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]

theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y

def defaultDecor : Decor := (zero,0,0)

theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp

theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)

def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])

theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])

theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel

theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel

theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel

theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel

theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel

theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel

theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel

theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel

theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel

theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r

theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))

theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction

theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)

def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a

def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl

theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))

theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951

def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov

def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)

def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1

theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl

def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b

def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _

theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _

theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]

theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))

def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst

theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h

def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)

def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]

theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)

theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p

theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)

def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)

def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)

def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values

theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask

def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)

def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n

theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws

theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2

def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old

theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h

theorem baseKnown : Known [] := by simp [Known]

def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v

def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)

def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)

theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)

theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]

theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]

theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]

theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]

theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]

theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]

theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r

theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)

set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat

abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)

def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)

def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)

theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor

theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor

def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb

def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs

theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov

def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)

def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)

theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)

theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat

theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool

def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))

def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb

theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h

def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true

def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)

def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)

theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)

def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)

def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))

theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d

theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d

theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d

theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap

def g15d3 (i : Nat) : Nat := 0xf

def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)

def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]

def g15columns : IndexTree ColumnInfo := (.leaf [])

def g15autos : Array (List Nat) := #[[],[33,48]]

def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking

def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none

def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩

def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d

def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00

def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)

def g31d6 (i : Nat) : Nat := 0x11a20bf

def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)

def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]

def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))

def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]

def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking

def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none

def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩

def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]

def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])

def g47autos : Array (List Nat) := #[[],[83,32]]

def g47levels : Nat → Packing
  | _ => emptyPacking

def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩

def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]

def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])

def g55autos : Array (List Nat) := #[[],[84]]

def g55levels : Nat → Packing
  | _ => emptyPacking

def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩

def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]

def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])

def g63autos : Array (List Nat) := #[[],[50,65]]

def g63levels : Nat → Packing
  | _ => emptyPacking

def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩

def g111d6 (i : Nat) : Nat := 0x120ff

def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)

def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]

def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])

def g111autos : Array (List Nat) := #[[],[83,32]]

def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking

def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none

def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩

def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]

def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])

def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]

def g119levels : Nat → Packing
  | _ => emptyPacking

def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩

def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1

def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00

def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)

def g189d7 (i : Nat) : Nat := 0x1f5859bf

def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)

def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]

def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))

def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]

def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking

def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none

def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩

def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]

def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])

def g127autos : Array (List Nat) := #[[],[101,66,16]]

def g127levels : Nat → Packing
  | _ => emptyPacking

def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩

def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044

def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380

def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081

def key191l7 (i : Nat) : Nat := 0x2c

def g191d6 (i : Nat) : Nat := 0x47d6448788a00

def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)

def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600

def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)

def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600

def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)

def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00

def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)

def g191d10 (i : Nat) : Nat := 0x1f3c11ff

def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)

def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]

def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))

def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]

def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking

def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none

def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩

def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]

def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])

def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]

def g251levels : Nat → Packing
  | _ => emptyPacking

def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩

def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]

def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])

def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]

def g255levels : Nat → Packing
  | _ => emptyPacking

def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩

def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008

def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040

def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280

def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085

def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600

def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)

def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600

def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)

def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600

def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)

def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00

def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)

def g383d12 (i : Nat) : Nat := 0x11b280e4ff

def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)

def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]

def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))

def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]

def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking

def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none

def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)

def maps3 : List (Nat × List Nat) := []

def known3 := extendKnown [] 1 maps3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)

def maps7 : List (Nat × List Nat) := []

def known7 := extendKnown known3 2 maps7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl15_3 : block g15 3 0 1 = true := s15_3_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]

def known15 := extendKnown known7 4 maps15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)

def maps45 : List (Nat × List Nat) := []

def known45 := extendKnown known15 3 maps45

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)

def maps51 : List (Nat × List Nat) := []

def known51 := extendKnown known45 3 maps51

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl31_6 : block g31 6 0 1 = true := s31_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]

def known31 := extendKnown known51 7 maps31

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]

def known47 := extendKnown known31 5 maps47

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]

def known55 := extendKnown known47 5 maps55

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]

def known63 := extendKnown known55 8 maps63

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl111_6 : block g111 6 0 1 = true := s111_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]

def known111 := extendKnown known63 7 maps111

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]

def known119 := extendKnown known111 6 maps119

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl189_7 : block g189 7 0 1 = true := s189_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]

def known189 := extendKnown known119 8 maps189

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)

def maps250 : List (Nat × List Nat) := []

def known250 := extendKnown known189 5 maps250

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]

def known127 := extendKnown known250 9 maps127

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl191_6 : block g191 6 0 1 = true := s191_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl191_10 : block g191 10 0 1 = true := s191_10_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]

def known191 := extendKnown known127 11 maps191

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]

def known251 := extendKnown known191 8 maps251

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]

def known255 := extendKnown known251 12 maps255

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem bl383_12 : block g383 12 0 1 = true := s383_12_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]

def known383 := extendKnown known255 13 maps383

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)

def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c

def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001

def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)

def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022

def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27

def hashdeadl9 (i : Nat) : Nat := 0x202e0

def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02

def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)

def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600

def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)

def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)

def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)

def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))

def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)

def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600

def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)

def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00

def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)

def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff

def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)

def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]

def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))

def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking

def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none

def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩

set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead8 : block dead 8 0 2=true := sdead8_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem alldead14 : block dead 14 0 1=true := sdead14_0

theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14

theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

-- Fixing vertices restricts every live wire to a smaller truth table. Each live
-- wire made constant saves a gate. An induced graph can retain the free first OR
-- when both endpoints survive. Check these lower bounds from smaller graphs up.
-- The finite search uses all 512 input rows and 768 opposite-output row pairs.
def firstOr := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)

def roots (m : Nat) (extra : Bool) :=
  if extra then vars m ++ [firstOr] else vars m

def pairHints (s h : Nat) : List (Sig × Row × Row) :=
  (selected s).map fun (i,a) =>
    let r := (h >>> (9*i)) &&& 511
    (a, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))

def auxColumnOK (m z o q s hints lb base : Nat) (aug endAug : Bool) :=
  let ms := fixRows z o
  let free := colFree m z o
  let T := graphGoal m
  let G := movedWord ms T
  let xs := pairHints s hints
  let mid := roots free (aug && free.testBit 0 && free.testBit 4)
  properB G && checkMap ms (roots m aug) T mid G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G mid xs && decide (lb ≤ (xs.map Prod.fst).toFinset.card-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G mid (roots q endAug) (graphGoal q) xs &&
       decide (lb ≤ base+(xs.map Prod.fst).toFinset.card))

theorem auxColumn {m z o q s hints lb base aug endAug}
    (h : auxColumnOK m z o q s hints lb base aug endAug = true)
    (prior : Lower (roots q endAug) (graphGoal q) base) :
    Slice (roots m aug) (graphGoal m) (subcube z o) lb := by
  simp only [auxColumnOK,Bool.and_eq_true,beq_iff_eq] at h
  apply slice_correct h.1.1.2 h.1.2 (proper_of _ h.1.1.1)
  by_cases eq : q=0
  · simp only [eq,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    exact fun p w hr hit => h.2.2.trans (lower_count (proper_of _ h.1.1.1)
      _ h.2.1 p w hr hit)
  · have cut := h.2
    simp only [eq,ite_false,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact fun p w hr hit => cut.2.trans (lift_ok cut.1.2 (proper_of _ h.1.1.1)
      (proper_of _ cut.1.1) prior p w hr hit)

theorem lowerBlocks {v T L k t S} (hp : proper T) (bound : Lower v T L)
    (run : Live T k t S) (sub : ∀ a ∈ S, a ∈ v) : L ≤ k := by
  classical
  have r := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have sup : supply (v.map observe) (S.toList.map observe) := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,w,rr,hit,hs⟩ := contraction (observe_proper hp) r _ Reach.start sup
  have h := bound q w rr hit
  omega

theorem finishAug {m cap} (hints : Nat)
    (hp : proper (graphGoal m))
    (ess : checkEssential (graphGoal m) (roots m true) (pairHints m hints) = true)
    (v : (pairHints m hints).map Prod.fst = vars m)
    (no : Lower (vars m) (graphGoal m) (cap+1))
    (yes : Impossible (graphGoal m) cap (roots m true).toFinset) :
    Lower (roots m true) (graphGoal m) (cap+1) := by
  intro p bank h hit
  obtain ⟨k,t,S,small,run,sub⟩ := reach_live hp h hit
  by_cases he : firstOr ∈ S
  · have eq : (roots m true).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro ha
      change a ∈ vars m ++ [firstOr] at ha
      rcases List.mem_append.mp ha with old | last
      · have em := essential_ok ess a (List.mem_toFinset.mpr (v ▸ old))
        obtain ⟨r,s,diff,isolated⟩ := em
        exact raw_required run _ a sub r s diff isolated
      · simpa only [List.mem_singleton.mp last] using he
    by_contra! bad
    exact yes k t (by omega) (eq.symm ▸ run)
  · have sub' : ∀ a ∈ S, a ∈ vars m := by
      intro a ha
      have mem := sub a ha
      change a ∈ vars m ++ [firstOr] at mem
      exact (List.mem_append.mp mem).resolve_right fun h => he (List.mem_singleton.mp h ▸ ha)
    exact (lowerBlocks hp no run sub').trans small

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ordinaryFull : Lower (vars 511) (graphGoal 511) 15 := by
  apply lower_impossible (by unfold proper; decide +kernel) ?_ ?_
  · have ess : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 13438558465) = true := by decide +kernel
    intro a ha
    apply essential_ok ess
    have he : (graphPairs 511 13438558465).map Prod.fst = vars 511 := by decide +kernel
    rw [he]
    exact List.mem_toFinset.mpr ha
  · have h := dead_start (before_sound known383 valid383) geomdead tablesdead
    have e : graphGoal 511 = graph := by decide +kernel
    have v : vars 511 = inputs := by decide +kernel
    simpa only [e,v] using h

abbrev SliceCode := Nat × Nat × Nat × Bool
def cutDomain (c : SliceCode) := subcube c.1 c.2.1
def certifiedCuts (m : Nat) (cs : List SliceCode) :=
  ∀ c ∈ cs, Slice (roots m c.2.2.2) (graphGoal m) (cutDomain c) c.2.2.1

-- Each table lists the states left after applying the restriction bounds.
-- A hash selects a candidate child. The checker compares the actual wire sets.
-- The case certificates specialize the method used by JLDC in L-meta-2191.
def basic (q : Nat) := if q=511 then 15 else boundsBefore known383 q

theorem basicLower (q : Nat) : Lower (vars q) (graphGoal q) (basic q) := by
  by_cases h : q=511
  · subst q
    exact ordinaryFull
  · simpa [basic,h] using before_sound known383 valid383 q

def AugKnown (cs : List (Nat × Nat)) :=
  ∀ q, Lower (roots q true) (graphGoal q) (boundsBefore cs q)

theorem augEmpty : AugKnown [] := fun _ _ _ _ _ => Nat.zero_le _

theorem augExtend {q l cs} (hp : Lower (roots q true) (graphGoal q) l) (old : AugKnown cs) :
    AugKnown ((q,l)::cs) := by
  intro m
  by_cases eq : q=m
  · subst m
    simpa [boundsBefore] using hp
  · simpa [boundsBefore,eq] using old m

abbrev Packet := Nat × Nat
def asCut (v : Packet) : SliceCode :=
  (v.1 &&& 511,(v.1 >>> 9) &&& 511,(v.1 >>> 36) &&& 15,v.1.testBit 40)

def asCheck (m : Nat) (old : List (Nat × Nat)) (v : Packet) :=
  let c := asCut v
  let q := (v.1 >>> 18) &&& 511
  let s := (v.1 >>> 27) &&& 511
  let ea := v.1.testBit 41
  let lo := if ea then boundsBefore old q else basic q
  auxColumnOK m c.1 c.2.1 q s v.2 c.2.2.1 lo c.2.2.2 ea

theorem certifyPackets {m old} (prior : AugKnown old) (packets : List Packet)
    (ok : packets.all (asCheck m old)=true) : certifiedCuts m (packets.map asCut) := by
  intro c hc
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
  have h := List.all_eq_true.mp ok v hv
  apply auxColumn h
  cases eq : v.1.testBit 41 with
  | false => exact basicLower _
  | true => exact prior _

abbrev RowCode := Nat × Nat
abbrev Layer := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)

def emptyLayer : Layer := (0,0,0,0,0,0,0,0,fun _ => 0)
def lookupNode (layer : Layer) (h : Nat) : Option Nat :=
  let (n,_,_,_,buckets,slots,shiftBits,idxBits,data) := layer
  if n=0 then none else
    let off := packedAt data ((h % buckets)*shiftBits) shiftBits
    let slot := ((h/buckets+off)%slots)
    let v := packedAt data (buckets*shiftBits+slot*(idxBits+6)) (idxBits+6)
    let i := v &&& ((1 <<< idxBits)-1)
    if i<n && (v >>> idxBits)==h/(buckets*slots)%64 then some i else none

def nodeBits (layer : Layer) (depth ar i : Nat) :=
  let (_,_,_,_,buckets,slots,shiftBits,idxBits,data) := layer
  let start := buckets*shiftBits+slots*(idxBits+6)
  let width := depth*11+ar-10
  (packedAt data (start+10+i*width) width <<< 10) ||| packedAt data start 10

def nodeBank (seed : List Decor) (depth v : Nat) := decodeBank depth v seed
def nodeWires (seed : List Decor) (depth v : Nat) :=
  selectLive (v >>> (depth*10)) (nodeBank seed depth v)
def nodeValues (seed : List Decor) (depth v : Nat) := (nodeWires seed depth v).map Prod.fst

def dictionaryPairs (data : Nat → Nat) (cw rw idx dict : Nat) :
    Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let key := packedAt data pos idx
    let offset := dict+key*(cw+rw)
    (packedAt data offset cw,packedAt data (offset+cw) rw)::
      dictionaryPairs data cw rw idx dict n (pos+idx)

def nodeRules (layer : Layer) (depth ar i : Nat) :=
  let (n,pw,cw,rw,buckets,slots,shiftBits,idxBits,data) := layer
  let pos := buckets*shiftBits+slots*(idxBits+6)+10+n*(depth*11+ar-10)
  let start := packedAt data (pos+i*pw) pw
  let endPos := packedAt data (pos+(i+1)*pw) pw
  let header := pos+(n+1)*pw
  let size := packedAt data header 16
  let dict := header+20
  if size=0 then getPairs data cw rw (endPos-start) (dict+start*(cw+rw)) else
    let idx := packedAt data (header+16) 4
    dictionaryPairs data cw rw idx dict (endPos-start) (dict+size*(cw+rw)+start*idx)

def nodePool (m : Nat) (cuts : List SliceCode) (bank : List Decor) (ops depth : Nat)
    (rule : Nat × Nat) : Option BoundPool :=
  cuts[rule.1]?.bind fun c =>
    materialize (roots m c.2.2.2) (chosenSteps bank ops rule.2 depth) (cutDomain c) c.2.2.1

theorem nodePool_ok {m cuts bank ops depth rule pool} (hc : certifiedCuts m cuts)
    (h : nodePool m cuts bank ops depth rule=some pool) :
    ValidPool (vars m) (graphGoal m) pool := by
  unfold nodePool at h
  cases e : cuts[rule.1]? with
  | none => simp [e] at h
  | some v =>
    simp only [e,Option.bind_some] at h
    exact (materialize_sound (hc v (List.mem_of_getElem? e)) h :
      ValidPool (roots m v.2.2.2) (graphGoal m) pool)

def levelCtx (m : Nat) (seed : List Decor) (cuts : List SliceCode)
    (k depth i : Nat) (below here : Layer) : NodeContext :=
  let v := nodeBits here depth seed.length i
  let bank := nodeBank seed depth v
  let ws := selectLive (v >>> (depth*10)) bank
  let rules := (nodeRules here depth seed.length i).filterMap (nodePool m cuts bank v depth)
  let links := fun h => ((lookupNode below h).map
    (fun j => nodeValues seed (depth+1) (nodeBits below (depth+1) seed.length j))).toList
  (k,ws.length,ws,preCov ws,rules,links)

def testNode (m : Nat) (seed : List Decor) (cuts : List SliceCode)
    (k depth i : Nat) (below here : Layer) :=
  let ctx := levelCtx m seed cuts k depth i below here
  prelim (graphGoal m) ctx && testAll ctx ctx.2.2.1

def settled (m : Nat) (seed : List Decor) (k depth : Nat) (layer : Layer) :=
  ∀ i < layer.1, Impossible (graphGoal m) k
    (nodeValues seed depth (nodeBits layer depth seed.length i)).toFinset

theorem inLayer {layer h j} (ok : lookupNode layer h = some j) : j < layer.1 := by
  obtain ⟨n,pw,cw,rw,buckets,slots,shiftBits,idxBits,data⟩ := layer
  unfold lookupNode at ok
  dsimp only at ok ⊢
  split at ok
  · contradiction
  split at ok
  next valid =>
    simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
    exact Option.some.inj ok ▸ valid.1
  next => contradiction

theorem testNode_ok {m p q seed cuts k depth below here i}
    (pairs : properPairs (graphGoal m) (asRow p) (asRow q))
    (faith : ∀ w ∈ seed, faithful (asRow p) (asRow q) w)
    (good : certifiedCuts m cuts)
    (prev : settled m seed (k-1) (depth+1) below)
    (ok : testNode m seed cuts k depth i below here=true) :
    Impossible (graphGoal m) k (nodeValues seed depth (nodeBits here depth seed.length i)).toFinset := by
  simp only [testNode,Bool.and_eq_true] at ok
  have checks := ok.1
  simp only [prelim,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checks
  apply node_sound (raw:=vars m) pairs _ checks.1 (by simpa using checks.2) _ _ ok.2
  · intro w hw
    exact decode_faithful _ _ _ _ _ faith w ((selectLive_sub _ _).subset hw)
  · intro v hv
    obtain ⟨rule,_,hit⟩ := List.mem_filterMap.mp hv
    exact nodePool_ok good hit
  · intro tag ws h
    obtain ⟨j,found,e⟩ := Option.map_eq_some_iff.mp (show _ = some ws from by simpa using h)
    exact e ▸ prev j (inLayer found)

theorem basicAt {q l} (h : l ≤ basic q) : Lower (vars q) (graphGoal q) l :=
  fun p w hr hit => h.trans (basicLower q p w hr hit)

theorem excludeCard {T cap S} (sz : cap+1 < S.card) : Impossible T cap S := by
  intro k t hk run
  have h := (live_size run).2
  omega

theorem dropLower {m q extra s hints goal base}
    (hm : proper (graphGoal m)) (hq : proper (graphGoal q))
    (prior : Lower (roots q extra) (graphGoal q) base)
    (check : checkLift (fixRows (colFree m q 0) 0) (graphGoal m) (roots m true)
      (roots q extra) (graphGoal q) (pairHints s hints) = true)
    (le : goal ≤ base+((pairHints s hints).map Prod.fst).toFinset.card) :
    Lower (roots m true) (graphGoal m) goal :=
  fun p w hr hit => le.trans (lift_ok check hm hq prior p w hr hit)

def batchRange (m : Nat) (seed : List Decor) (cuts : List SliceCode) (k depth : Nat)
    (below here : Layer) (width start : Nat) :=
  let xs := (List.range (min width (here.1-start))).map fun j =>
    levelCtx m seed cuts k depth (start+j) below here
  let ar := (xs.head?.map fun c => c.2.1).getD 0
  if xs.all (fun c => c.2.1==ar) then xs.all (prelim (graphGoal m)) && runBatch k ar xs
  else xs.all (fun c => prelim (graphGoal m) c && testAll c c.2.2.1)

theorem batchRange_at {m seed cuts k depth below here width start i}
    (lo : start ≤ i) (hi : i < start+width) (valid : i < here.1)
    (ok : batchRange m seed cuts k depth below here width start=true) :
    testNode m seed cuts k depth i below here=true := by
  let xs := (List.range (min width (here.1-start))).map fun j =>
    levelCtx m seed cuts k depth (start+j) below here
  let c := levelCtx m seed cuts k depth i below here
  have mem : c ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i-start,List.mem_range.mpr (by omega),by simp [c,Nat.add_sub_of_le lo]⟩
  let ar := (xs.head?.map fun v => v.2.1).getD 0
  change (if xs.all _ then xs.all _ && runBatch k ar xs else xs.all _) = true at ok
  change (prelim _ c && testAll c c.2.2.1)=true
  split at ok
  next aligned =>
    obtain ⟨j,hj,e⟩ := List.getElem_of_mem mem
    have eq : c.2.1=ar := beq_iff_eq.mp (List.all_eq_true.mp aligned c mem)
    have hc : xs[j].1=k := by rw [e]; rfl
    have ha : xs[j].2.1=ar := e ▸ eq
    have hn : xs[j].2.2.1.length=ar := by rw [e]; exact eq
    simp only [Bool.and_eq_true] at ok ⊢
    exact ⟨List.all_eq_true.mp ok.1 c mem,e ▸ runBatch_at hj hc ha hn ok.2⟩
  next => exact List.all_eq_true.mp ok c mem

def strips (p : Nat → Bool) (w : Nat) : Nat → Nat → Prop
  | 0,_ => True
  | n+1,i => p i=true ∧ strips p w n (i+w)

theorem strips_at {p width n start} (h : strips p width n start) (i : Nat)
    (lo : start ≤ i) (hi : i < start+n*width) :
    ∃ j, j ≤ i ∧ i < j+width ∧ p j=true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    rw [Nat.succ_mul] at hi
    by_cases small : i < start+width
    · exact ⟨start,lo,small,h.1⟩
    · exact ih h.2 (by omega) (by omega)

theorem advanceBatch {m p q seed cuts k depth below here width groupsN}
    (pairs : properPairs (graphGoal m) (asRow p) (asRow q))
    (faith : ∀ w ∈ seed, faithful (asRow p) (asRow q) w)
    (good : certifiedCuts m cuts)
    (prev : settled m seed (k-1) (depth+1) below)
    (sz : here.1 ≤ groupsN*width)
    (h : strips (batchRange m seed cuts k depth below here width) width groupsN 0) :
    settled m seed k depth here := by
  intro i hi
  obtain ⟨j,lo,lt,check⟩ := strips_at h i (Nat.zero_le _) (by omega)
  exact testNode_ok pairs faith good prev (batchRange_at lo lt hi check)

def sampleCols189 : Array (Bits × Bits) := #[(0x6f3b66eaf362ffda1fefd21cef794b4b7ffd6f99656aee37cebd5f26f13d9b379b18a97e3ff6c2e5f45a8b7fb5a812e7afdb56573eed3751c94be160ef8ba562fd62f9446ea1598edde4d784eecb9ab4a36c7781ee2e619d2390729ab721e710,0x9040881508b940290001010014016210a4051442930044481050a8d58a50849b2c5600a80c2809804648008820a00140a45301301348a054514908150b8609450a4315368800090c08a04500ae4108952d645ab122006017211562829120e310),(0x0,0x0),(0xe6edee98f5f53dfbad5bce3bb313f6851e7fa33fbf36ddf1fe7287d3decde38e7931551dfd96ffca37d93d5a911b8d0a5cf72e0fb7376ffe55bf997f12dd787029c54c0b86f6277ddf4f2f86037079e8e697d67162948ae4b00f21fd090efd81,0x1191167880b474443249448018801000080410800a412108184cc1e255a106d8886060140d49052189090431c08201211044a0100230d00586105854986aa2048805ac942200621874d2a84000020482211500356bd90a49115007d0102bd80),(0xe1ffd113e98feff7f5b3bddebc96fcc6fd8edbf8d5b5f14d44f1655f14f5feed38a336fbda197aeacbab469f56cf67d3d0fcb954f5c5c7e334ef22d305f8bbf13ad58c9a394a9a193977e94b7877fb48bcaeba1652d0af03e42ca962da727065,0x1e000c8836f0000808420002184042a0c84804041c488c00226a10e0daa184923750c8d010200e0c8408489000a50581009121c0a188005a030a901a262815482266a536884210083022814a486610069cee0ad02000690362682902da604061),(0xbb39d1fe3fb942c9f0eff1eb7cfdc7fef39d2768ca9efb3cfd7afd68b2f0dfdb9942a2e4fe7b855fc8ddc6c5bbe6ee2dfbce86a9cdd23bf3c22c23f3c7a6a3d17f36b8d439b7da67a6f830bb66d4857c1325bc875cce3d4e44b09e54a03594f6,0x40862202c106b2c245140e04231004060190a080202100820405470a250e7b2440a92200e242b030302136259140680e030008000420032020b461601011a2b0d5884ac961a4c06200503090001081680201a50e5c9c94e81c82945420151486),(0x9fea3c4d01bffec4d70f3d3e7fc7effbee5fdfd73fdd26f203879a944102dfbf3ffc1e02c3c3b079f9eff3f8eefd9df5f43b77f2721f930c7b53c40c2800a7feffcef72066a8a4e324bedd7d9dab67c3a8c84108d1adfddd7b40d42b5fc016aa,0x4035032ab64209802480588d82b0110401206208001030208006540a74a93064d180d0038306206028a0a4640d084018420c440140141e000222830aa468f2206084eac96488a0c3040c0805008047088299010c58ad9980d26894290ec014a0),(0x0,0x0),(0xb6afbbefae536ded4a54aeef4fabdd778fbc74765a7ff4fbf74f9e9c6eff12865ce47d9ffbaecd1606b478627ad9fcfd8732d9aaf8faf8ed63335d5c3ab77a5c538ec621995ffdfe5a092afc9d2f049348ddecf92385346878434f8550fd498a,0x8a40441041b4b01100400000000480c8620f08510f0801444a3123e18204cf92227908641c0847840200080002048421a02230f23200808fa51c6070021101d2175205369013181458000028152b00831966aef0200024592c824b80503d400a),(0x0,0x0)]
def pos189 (j : Nat) := (sampleCols189[j]?.getD (0,0)).1
def neg189 (j : Nat) := (sampleCols189[j]?.getD (0,0)).2
def raw189 := rawDecor 189 pos189 neg189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs189 : properPairs (graphGoal 189) (asRow pos189) (asRow neg189) :=
  chart_pairs (m:=189) (p:=pos189) (q:=neg189) (by decide +kernel) (by decide +kernel)
def pk189 : List Packet := [(0x5002f00001,0x0),(0x5002e40004,0x0),(0x5002d40008,0x0),(0x500a700020,0x10),(0x5000f40080,0x0),(0x4002b00011,0x0)]
def cuts189 := pk189.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert189 : certifiedCuts 189 cuts189 :=
  certifyPackets augEmpty _ (by decide +kernel)
def layer189_6 : Layer := (6,3,3,0,2,10,1,3,(fun i => 0x3410000046da22fd56bf51afd26bf45bdd34fe40930036d1b4062ce21d606033f6))
def pred189_6 := batchRange 189 raw189 cuts189 6 2 emptyLayer layer189_6 12
theorem cases189_6_0 : pred189_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved189_6 : settled 189 raw189 6 2 layer189_6 :=
  advanceBatch pairs189 (raw_faithful 189 _ _) cert189 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases189_6_0,True.intro⟩
def layer189_7 : Layer := (1,3,3,0,1,2,0,1,(fun i => 0xb1a20000147f4c2001))
def pred189_7 := batchRange 189 raw189 cuts189 7 1 layer189_6 layer189_7 12
theorem cases189_7_0 : pred189_7 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved189_7 : settled 189 raw189 7 1 layer189_7 :=
  advanceBatch pairs189 (raw_faithful 189 _ _) cert189 solved189_6 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases189_7_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra189 : Lower (roots 189 true) (graphGoal 189) 8 := by
  apply finishAug (cap:=7) 0x20000201020200010 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=189) (l:=8); decide +kernel)
  have eq : (nodeValues raw189 1 (nodeBits layer189_7 1 raw189.length 0)).toFinset = (roots 189 true).toFinset := by decide +kernel
  exact eq ▸ solved189_7 0 (by decide +kernel)
def past189 : List (Nat × Nat) := (189,8)::[]
theorem pastOK189 : AugKnown past189 := augExtend extra189 augEmpty
def sampleCols215 : Array (Bits × Bits) := #[(0xf5d6efec27cffbbf31965ffabf7d59afe6657f75f02bb8b525bfaf5ca1de9dbdd6e3287b7ffefcb8681d5df7f9183bfbe185dbec27fd6e3073595fe2fcbbece75260f89dffa11a73aea873fa33cbd9c7bf0327fd1c11fa842f06b9e2c592339b,0x12250822c4200480002860642000021222c20483d744614d4a24408500110185466030443010c420102092142a16090000100c6501316849125c88a9a5202125b0aa380167800040228810a80049c8c55f1200cd08d322408d2230e04482130b),(0x4fbfbdfd7ef377ee3a2be7fb59ffaef7ebd493daddb7f5df56d7fbbdfe2bef19b77c85ad937fb7e68de6fed7fc2bd6d7f87a7df4d8ece9dcee1aefff9c55f3f189f9dd271bba6d9dceef8e5ecdcc662149ccba7b5b8f1e31db5d5a2dd8f549e8,0x208001000808d81464540508028400000000410020000030a102124a0802200800080108084c10c3228701831020901d2202000000040200002004124a8042404154410010280d05c4248802088002002008b2227124480012084a01883408a0),(0x9b4bdfbb9f1ebebefd69bf5c56b1c7d9737fe7f39edd37799b4b30da5da47be68c60dffeae0dfe97d7fa2a39baedaeaf573d27c79f9fb1e790f73eb97f4ee38825873262d57dd50e731a57b7ff7f87180438dc8db2ecb36af5f044d776299e5d,0x280204909a37267b91b32a241200038000008454e346db5c000000000000020000108044128081c0d9d2bc25999efe1ca0200a0010000ccb536b5b812ab00000011000003025235f77f0008000200880699b776edb000867601145d),(0x0,0x0),(0xf4bd57ec9ba9687d2df77265a838fd5dbedbff85f15d98756b3425001b7f76bfdbdf77b2edfb39cd67bb0d9e0d952b4048ad901e357d7e00135ff79affb69c065200efdaacb5a6ef4f33f831a610ffc6b7075db8153cf8966003ef862102f8f6,0x402160d115d0132a24489984cdc308041200238009b96b2b1dbbf7ad1085230981206108d8a2188265205421040c674eccb81008a0a00a0a48377125adfd6da4f5584ca882084ab48312810a610050aa045df30d52cd83f7299cf062100e8f4),(0x0,0x0),(0xd4b488bbfb6b56e7ef7ecfc7fed6faa33da4a798810541127385532bbb5b0946ab9fa8cfb43b0f5abcd6dcdaa77bfa111fdb48d9d562b0a81e17ca1f8ff997f088182da7a94eaee130d7fdcda9f7382855c50c5b41563c1de93b92181a46f37d,0x8878f2cc0400060a10039a81800100698048a8bfdbffbb4d5efda595c2410a24d225ca87c4a244209148e860c5c1600200006280544139b2125ffba9b57fbdbfbeab2826a946a2a0208245410106304b57e54ddd0a5ab71fed3390181242f35d),(0x6ee9faeec436bd34ffddbafdf7df37265f2aac78124412098b6da5cf46f4f45e6fdadac3f6b676b75e97a7aaeac76dadf74ba6e36a1250a300fcb3216feff7682406025866c6f3fefdfdadeb5ebf009807304d15b866694b77a82579ae0aefa5,0xd11d45f0b9234aa4141804104640000000111005fd7df5ba31cb924a0024048301c575926370b3598c9176a1e222142986400000000004045a5fff334ac94247ed5402100484725e1c59a5ca088000049fbd7d77b966480912082579880aeba0),(0x0,0x0)]
def pos215 (j : Nat) := (sampleCols215[j]?.getD (0,0)).1
def neg215 (j : Nat) := (sampleCols215[j]?.getD (0,0)).2
def raw215 := rawDecor 215 pos215 neg215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs215 : properPairs (graphGoal 215) (asRow pos215) (asRow neg215) :=
  chart_pairs (m:=215) (p:=pos215) (q:=neg215) (by decide +kernel) (by decide +kernel)
def pk215 : List Packet := []
def cuts215 := pk215.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert215 : certifiedCuts 215 cuts215 :=
  certifyPackets pastOK189 _ (by decide +kernel)
def layer215_6 : Layer := (1,0,0,0,1,2,0,1,(fun i => 0x7f4c00b2))
def pred215_6 := batchRange 215 raw215 cuts215 6 1 emptyLayer layer215_6 12
theorem cases215_6_0 : pred215_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved215_6 : settled 215 raw215 6 1 layer215_6 :=
  advanceBatch pairs215 (raw_faithful 215 _ _) cert215 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases215_6_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra215 : Lower (roots 215 true) (graphGoal 215) 7 := by
  apply finishAug (cap:=6) 0x20080001000080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=215) (l:=7); decide +kernel)
  have eq : (nodeValues raw215 1 (nodeBits layer215_6 1 raw215.length 0)).toFinset = (roots 215 true).toFinset := by decide +kernel
  exact eq ▸ solved215_6 0 (by decide +kernel)
def past215 : List (Nat × Nat) := (215,7)::past189
theorem pastOK215 : AugKnown past215 := augExtend extra215 pastOK189
def sampleCols31 : Array (Bits × Bits) := #[(0x59f7dd6a2b2a2e2d2d9ddafbbe4f5dee372bee7fd28d5ee7aed47d5678b3efbad456545c5a5b3bb5f77c9ebbdc6e57dcffa51abdcf5da8faacf167df75a8aca8b8b4b6776beef93d77b8dcafb9ff4a357b9ebb51f559e2cfbeeb51595171696c,0x850c862a1164e0125822400039023198001280245010529143aa4003810a190c5422c9c024b04480007204633000250048a020a5228754800702143218a84593804960890000e408c660004a009140414a450ea9000e04286431508b270092c),(0xa6ff6c3c26a697fc541f2f3ddefd2bf93b54fbbfcdcd8c5fdf525f6a8b4dfed8784d4d2ff8a83e5e7bbdfa57f276a9f77f9b9b18bfbea4bed5169bfdb0f09a9a5ff1507cbcf77bf4afe4ed53eeff3736317f7d497daa2d37fb61e13534bfe2a0,0x822f00055ea011fc0000d0400004dc8650000090b25e525280014b4001045e000abd4023f80001a0800009b90ca000012164bca4a5000296800208bc00157a8047f0000341000013721940000242c979494a00052d00041178002af5008fe000),(0x3f1bfcd4949588d3fc37d7e86f7ebebd5f9f1dcfad7b975c91d8e6ff147e37f9a9292b11a7f86fafd0defd7d7abf3e3b9f5af72eb923b1cdfe28fc6ff3525256234ff0df5fa1bdfafaf57e7c773eb5ee5d7247639bfc51f8dfe6a4a4ac469fe1,0xfc00015f8003fc08282780000360af000000000025ad7fc000be000001f80002bf0007f810504f000006c15e00000000004b5aff80017c000003f000057e000ff020a09e00000d82bc000000000096b5ff0002f8000007e0000afc001fe0),(0xf8febae5d0515b4aa2feb9f6f7cce7f4dde777f6233a753675bbc38de7f1fd75cba0a2b69545fd73edef99cfe9bbceefec4674ea6ceb77871bcfe3faeb9741456d2a8bfae7dbdf339fd3779ddfd88ce9d4d9d6ef0e379fc7f5d72e828ada5517,0x30b20067b6005a4802a146000423081f000640046bc51040001e6001c0616400cf6c00b49005428c000846103e000c8008d78a2080003cc00380c2c8019ed80169200a851800108c207c00190011af14410000798007018590033db002d24015),(0xc72df767494871159bcfe4277fbfdf5e8effe9f1f24e67ad623f78b1ff8e5beece9290e22b379fc84eff7fbebd1dffd3e3e49ccf5ac47ef163ff1cb7dd9d2521c4566f3f909dfeff7d7a3bffa7c7c9399eb588fde2c7fe396fbb3a4a4388acde,0x450d340048e9a11498501998000804e060000161002aca16e3c01000068a1a680091d3422930a03330001009c0c00002c20055942dc78020000d1434d00123a6845261406660002013818000058400ab285b8f0040001a2869a002474d08a4c2),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def pos31 (j : Nat) := (sampleCols31[j]?.getD (0,0)).1
def neg31 (j : Nat) := (sampleCols31[j]?.getD (0,0)).2
def raw31 := rawDecor 31 pos31 neg31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs31 : properPairs (graphGoal 31) (asRow pos31) (asRow neg31) :=
  chart_pairs (m:=31) (p:=pos31) (q:=neg31) (by decide +kernel) (by decide +kernel)
def pk31 : List Packet := [(0x4000780001,0x0),(0x4000740002,0x0),(0x40006c0004,0x0),(0x40005c0008,0x0)]
def cuts31 := pk31.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert31 : certifiedCuts 31 cuts31 :=
  certifyPackets pastOK215 _ (by decide +kernel)
def layer31_5 : Layer := (6,3,2,0,2,9,3,3,(fun i => 0xd300000922445f956fa6b7d25be8aef453f206a001ac799ba6b7d0b20301a0))
def pred31_5 := batchRange 31 raw31 cuts31 5 2 emptyLayer layer31_5 12
theorem cases31_5_0 : pred31_5 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved31_5 : settled 31 raw31 5 2 layer31_5 :=
  advanceBatch pairs31 (raw_faithful 31 _ _) cert31 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases31_5_0,True.intro⟩
def layer31_6 : Layer := (1,2,2,0,1,2,0,1,(fun i => 0xe4000033f5000b6))
def pred31_6 := batchRange 31 raw31 cuts31 6 1 layer31_5 layer31_6 12
theorem cases31_6_0 : pred31_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved31_6 : settled 31 raw31 6 1 layer31_6 :=
  advanceBatch pairs31 (raw_faithful 31 _ _) cert31 solved31_5 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases31_6_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra31 : Lower (roots 31 true) (graphGoal 31) 7 := by
  apply finishAug (cap:=6) 0x1020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=31) (l:=7); decide +kernel)
  have eq : (nodeValues raw31 1 (nodeBits layer31_6 1 raw31.length 0)).toFinset = (roots 31 true).toFinset := by decide +kernel
  exact eq ▸ solved31_6 0 (by decide +kernel)
def past31 : List (Nat × Nat) := (31,7)::past215
theorem pastOK31 : AugKnown past31 := augExtend extra31 pastOK215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra159 : Lower (roots 159 true) (graphGoal 159) 8 := by
  exact dropLower (q:=31) (extra:=true) (s:=128) (hints:=0x20000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra31 (by decide +kernel) (by decide +kernel)
def past159 : List (Nat × Nat) := (159,8)::past31
theorem pastOK159 : AugKnown past159 := augExtend extra159 pastOK31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra223 : Lower (roots 223 true) (graphGoal 223) 9 := by
  exact dropLower (q:=159) (extra:=true) (s:=64) (hints:=0x80000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra159 (by decide +kernel) (by decide +kernel)
def past223 : List (Nat × Nat) := (223,9)::past159
theorem pastOK223 : AugKnown past223 := augExtend extra223 pastOK159
def sampleCols243 : Array (Bits × Bits) := #[(0xbdf78f3def76bf3ffbf285875dfdad39febf9b7bab9cf75f4fffbd6dd9fec39ebbc3f8db7eafcdfebefa2fa3a56d76e19e9feffb0a1f2ebf1f1af6f97e5eeb8cad55db3ef47a70df7d4cfa6fa541b1c1f997575c93d6cd14b6cf49f255c3547a,0x8400021110880181102882108422001600010440808200000919220312014080008080408424002112080000c20e211100c18041820116010480000820a49860008200422201004405825810031c96850924400020820104701404442042a),(0xe6ffddcae59647eff77b787cf7bf91f64dfb9e385dab3fe732db1f036bafc7f1fe3f344ee77cdb57e1cb5bbe7ab896f42b62f9fed170f95fef757dbb9a3123b60626eecd578fb6a7bfbbca92b1be4112091a8227e34bfb2f4fb83279f859b3b4,0xb1024000a20210120261010002004412606b0a1a9c66092c5264808810a04a810a91120c0110c2c84428928288080000208e0a260c0c1889280134d1c242586114f404441048083199b020230344000032841118761b31d07b0203998093314),(0x0,0x0),(0x0,0x0),(0x5f17ef5bf19fbdb797cbfb1aef983db1a5e17e82a0c4c484510b51f865751debc5cf837fe53641d933a23d95fc56f4eecbd53caa9d66fec9699eecd0603eae0a111f8de2b69e37a317635192f2fd6c6b12f50fcb231c614e2255d2a0328dfd6,0x52a0890a42c402024342242142c1188d800d502eb9f7b5d7fb7f6e2dc00c0920e130a2070a63109ac80c42333351c500442c410201a3456c97a7b7edbe3971b679ff80982249412a2126211822294206952f4cb9fa7dd75d6ab05c2a0328dbd4),(0x7b72325cf1fbfbac7d9dbfcefbfb7efdefbf7cdfec75b496da26d1f735a83e6a73a337a499a470a15edeb4ddc6ef2dfb7fbe7f97ffef5c7db687b36cf9ee1e6958c8372dcbd5d900c8493dfffefd6f2fcfee2db98ead01c91046e69586aedb09,0x213320a944e004538060403100040010081084601182040c5eb76608c400124a320234a489a410a04d6483001900500008409220880489000409a27eba21609608d9320d8bd1d900c809000004000400008625b88e2d054b672046958084db00),(0x7a3cfeaabee65fd3069bffb1151f7edb55ebf4e0593618a2e3625e0b4ef72e633c5dcfccae579bf79365dcf9193abd15b3f4d25d576bcd14e2f62f2fb633637202223df19f6c1ffaceb7d2f8da22ba13884a982ef00f726e69359acd2c32eee4,0x84820004841c50d409100b429a5501200191091c56399f4c1ad8b5f752c1184688064051238c0303312060c00021343961e4045016253c772417eca0e313ca79eeb03d0018281668c40090d8ca02a067d8d6b8ee701e486278059ac42432cce0),(0xffba61535bed5878eefef67bbb5dc226ff0efdec14c79412da0e6592b6f0f9c74ff9b7fdaf8cae1cec55c046e6d2e9db70f725b7edd2d1653287f9ccadb15fc15088052268b7ef7df7bfc7054add6faecf6828ed0e3148f50896a506fa2e0df5,0x5c044c000800800812088984a8ba22c842aa0a9b6e3dfaf3a148995731a0641045c54b1264528554200108024414084a24920985334a167dbad65d8104520b69f7260522400422543234c60108cd0b2fef691a473112ea3408d6a1027a2a04f5),(0x0,0x0)]
def pos243 (j : Nat) := (sampleCols243[j]?.getD (0,0)).1
def neg243 (j : Nat) := (sampleCols243[j]?.getD (0,0)).2
def raw243 := rawDecor 243 pos243 neg243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs243 : properPairs (graphGoal 243) (asRow pos243) (asRow neg243) :=
  chart_pairs (m:=243) (p:=pos243) (q:=neg243) (by decide +kernel) (by decide +kernel)
def pk243 : List Packet := []
def cuts243 := pk243.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert243 : certifiedCuts 243 cuts243 :=
  certifyPackets pastOK223 _ (by decide +kernel)
def layer243_6 : Layer := (1,0,0,0,1,2,0,1,(fun i => 0x7f480001))
def pred243_6 := batchRange 243 raw243 cuts243 6 1 emptyLayer layer243_6 12
theorem cases243_6_0 : pred243_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved243_6 : settled 243 raw243 6 1 layer243_6 :=
  advanceBatch pairs243 (raw_faithful 243 _ _) cert243 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases243_6_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra243 : Lower (roots 243 true) (graphGoal 243) 7 := by
  apply finishAug (cap:=6) 0x100080201000000210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=243) (l:=7); decide +kernel)
  have eq : (nodeValues raw243 1 (nodeBits layer243_6 1 raw243.length 0)).toFinset = (roots 243 true).toFinset := by decide +kernel
  exact eq ▸ solved243_6 0 (by decide +kernel)
def past243 : List (Nat × Nat) := (243,7)::past223
theorem pastOK243 : AugKnown past243 := augExtend extra243 pastOK223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra247 : Lower (roots 247 true) (graphGoal 247) 9 := by
  exact dropLower (q:=231) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=231) (l:=8); decide +kernel) (by decide +kernel) (by decide +kernel)
def past247 : List (Nat × Nat) := (247,9)::past243
theorem pastOK247 : AugKnown past247 := augExtend extra247 pastOK243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra251 : Lower (roots 251 true) (graphGoal 251) 8 := by
  exact dropLower (q:=243) (extra:=true) (s:=8) (hints:=0x80000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra243 (by decide +kernel) (by decide +kernel)
def past251 : List (Nat × Nat) := (251,8)::past247
theorem pastOK251 : AugKnown past251 := augExtend extra251 pastOK247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra63 : Lower (roots 63 true) (graphGoal 63) 8 := by
  exact dropLower (q:=31) (extra:=true) (s:=32) (hints:=0x200000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra31 (by decide +kernel) (by decide +kernel)
def past63 : List (Nat × Nat) := (63,8)::past251
theorem pastOK63 : AugKnown past63 := augExtend extra63 pastOK251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra183 : Lower (roots 183 true) (graphGoal 183) 8 := by
  exact dropLower (q:=167) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=167) (l:=7); decide +kernel) (by decide +kernel) (by decide +kernel)
def past183 : List (Nat × Nat) := (183,8)::past63
theorem pastOK183 : AugKnown past183 := augExtend extra183 pastOK63
def sampleCols187 : Array (Bits × Bits) := #[(0xdff7c76fe3cee8ce7fff7f4673a5f64de1fffff6dd6bfebefef9bcb791c5abe3fed46ffbfccdcde91afbbb863e3de76782ef77ffb527bd7bef3adffdb9b14d990e67ecdcf9b3c97fef603deae14672e07944e89df8caecd2dfcd7076e9e17274,0x102004100449120205902004530000a600002802810000002448c8120280403220000800404420400a22000405012689800148c80412030080400082c844170800080008214010a2602582204012ea2900c4089000004018692040a8a04214),(0x2ef34cd39adddc219fff2e1caf7fde69fc31dfb402c92a9088f874833f2c62fb75cb4de9ba2b4c669579998de1e2d576f0332f3f7715d2fb0fb5d5ae788649a80845a6dac76f75ff48e150673ab93740d041f20ba5ca6d71a794aa35c03dbfe0,0x4144810080608404a00826c941004ed2006f2095fc7eff7b7f5b9717c51c2c084c871346991818ca032088902062c0805014421334c881f4e67dbfde78161be8f7ff2608c50614a74881106008990101d4db33876fdb7f33a7908a35401dbde0),(0x0,0x0),(0xf43cfb5f9dfbf47bee16e17ff155c3f7972dca88189225234b76d70765b3ddd9a42af2fb8bdab977659c7c719caedafd7ad78df24993da65d4dcaf16d8cecb6250885f639d533ed43eb3cf54b7d47d47d5396722e3852a242a3ae7283c98eec9,0x4a61401859004a3824923401089c28016004917533e396d426be5afc186b08850680582042a6c03070303a50888a00448e060c82e09232cbc6f14a8dc48d4d57cdc10c421451024424b24944b51028775d15d661f2c121609a38e5203c986e48),(0xf3fef0bdfde57fffe93d3ebfd04afc7fd31abed82db3c677323edf8ef4b3883ffeaab705ffd286bf6583eff153df7eea357ad8f5467ffdb5b6dbecd4d0cf8ee3528afd1f3d0cfe0bb18fccbea6af8da5e56b6fa23b0c1ea6693296da1b14d9ad,0x4008e01028890414020091240209142088122024c0c292ac941a503e0803012811926112811204d8c810524211068802058402404090034210cb552382220a8323ec1112108ac091105003002270400826a29920d2c5e932182129a030491a1),(0x85b92bfdd6377ffe37bdf5ff6fbffdf62cf7b133fe46bb684d255afe4b5c751c8955cd1606ed3737ca5fee5acfff5b97fffee70faffba2f6e66db34ba7bc7c74a53042f942de8280f7ffb3fdd97bcf5aded731564cf99119185b598536deb512,0x35035b022bc00001c0420a040000022400109004000a82655f9ba5018010411c88404d16002fb000af8011a00000b200002280001333a000964ba36e7002018805bb40f902de80804000800c8000cd004405217648fd11b1270251851052b500),(0x0,0x0),(0x4b4d9fbc2b1ff751d77ebaa1bd9aebffaed6ebd52a0e33682d1345ccafca57ffe77555c5c93c7298ba26642eefde211f7d50bfc79efe5aa664e5fada6e8a3dc4a1101b277efdfdff481e23915d7b8ada9ad3544236b91b4b88910dcbc68e4fe2,0x2040000040920aa0115403a220ff41015220d3abfd17d9aa0645aae4b659421313e20a9f100088010004044428d081337c8250d08404ef768b45c90898ccc77fa4412065800795a080a0291516a025ebbf25e08b7022e4288d90c4ac68c4ae2),(0x0,0x0)]
def pos187 (j : Nat) := (sampleCols187[j]?.getD (0,0)).1
def neg187 (j : Nat) := (sampleCols187[j]?.getD (0,0)).2
def raw187 := rawDecor 187 pos187 neg187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs187 : properPairs (graphGoal 187) (asRow pos187) (asRow neg187) :=
  chart_pairs (m:=187) (p:=pos187) (q:=neg187) (by decide +kernel) (by decide +kernel)
def pk187 : List Packet := [(0x150828c1000,0x1000000000),(0x5002e40002,0x0),(0x5002cc0008,0x0)]
def cuts187 := pk187.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert187 : certifiedCuts 187 cuts187 :=
  certifyPackets pastOK183 _ (by decide +kernel)
def layer187_5 : Layer := (1,2,2,2,1,2,0,1,(fun i => 0x6a0000033d5134c2e01))
def pred187_5 := batchRange 187 raw187 cuts187 5 2 emptyLayer layer187_5 12
theorem cases187_5_0 : pred187_5 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved187_5 : settled 187 raw187 5 2 layer187_5 :=
  advanceBatch pairs187 (raw_faithful 187 _ _) cert187 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases187_5_0,True.intro⟩
def layer187_6 : Layer := (1,2,2,0,1,2,0,1,(fun i => 0x120000067f4c2201))
def pred187_6 := batchRange 187 raw187 cuts187 6 1 layer187_5 layer187_6 12
theorem cases187_6_0 : pred187_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved187_6 : settled 187 raw187 6 1 layer187_6 :=
  advanceBatch pairs187 (raw_faithful 187 _ _) cert187 solved187_5 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases187_6_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra187 : Lower (roots 187 true) (graphGoal 187) 7 := by
  apply finishAug (cap:=6) 0x100000201080000210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=187) (l:=7); decide +kernel)
  have eq : (nodeValues raw187 1 (nodeBits layer187_6 1 raw187.length 0)).toFinset = (roots 187 true).toFinset := by decide +kernel
  exact eq ▸ solved187_6 0 (by decide +kernel)
def past187 : List (Nat × Nat) := (187,7)::past183
theorem pastOK187 : AugKnown past187 := augExtend extra187 pastOK183
def sampleCols191 : Array (Bits × Bits) := #[(0xedecee249bcb955b534ddc4ee12556725975ec4bf0b7b35bf8da6979cf98b46e162c4068612ece9c6a0e5b05a3e7c4a8e0f5daf16771ec1036f2aaa144992e2b100af2830bd4c1f7e8050a27ce83e6169c0e2b33592780e2c9349e851a9427c8,0x840a1204800a12101a12044ab06400932424c460181044511020424350c0942445234444000008104000010103828000401002900101640022c228204008222b5210d2010ac801524812020400802200800c003a5fa5008048048a81029420c8),(0x5fe26e7f1092c5babcfd9806963f077b52a11eab7bbde3fc750f3f99683d564f28881042491761d7c2cd704e24bed3d63f7bcf2b245c344cd8304c3ab86446f208e7a0841b26545e9ecd5e68cf067401eb933d45031155721ad0036e7979ed00,0x8c068026084c120a5cd13154b11434cda933b8fe7e3b8aa69471d18093542daa0882abbfff440c100c47046202c41920e28cc282048000c983000089840409001c7299c9527dc2db7cd7c38ef4e1c452b133904001055721090016e7949c500),(0x3235879f97e8fa2eb63ab6bd3efb119e24bba3fa4ffd4ce81ee726f0089bd2055b80951618d1271bfcf024b37b207ccedd8e374bdcd7d856880b3140033cf88438bd804564c45d101cba564d13aa4ac9d1b156d0e68c051567ea0088e6a6fa61,0x22018011064000021202c06030069812244440601014451594a8a2a1228a10011e54910000082200880000a010001c0001063143cc96985000000000010010041828804020c00010000002c50010c29ad0e08690bf800000276a008006263a60),(0xda8697bb4379e595b84e33f9e3212a8f9eb149dcaea6c836bda1d5f850e7cc5ceb118c90828099e85391e3760e662b35ca52915e7b8a462bc7ac7337d73997d617d62a3d574f0f0b994617d15a501aa80234600ec45f3c4c2405c94355d78413,0x8a45004019985488e81e0bc3b003c9d031950a8d8220e0681250544061e46c81236c77d094098852110250066200058840801012084622c4a872351030058387963a135e2e3f07dd27101052843801081c200e401f2c440005c94151d08411),(0xc953094bbdffb5d5678d832cca337acf9dc1fde4f1753c27a4c9f1407ae53a72ae1548888222d8a3ac3fab645119ff31158d69d484a819ab4e5eeb66acc6d9dd05eb4aadb35bc618e1c00dcd2c53d0e65605881c0850b3a9a309b1232b0b4b3a,0x6100080911442400240581a4080b50240a882a856265980e85cdada82e1e03033adc93882f6a8022a828a804501162301089094404a018880814014224c49844006904aca111c08822c0cdc9ad73c4ce72a19f8020409329a3083022280b4b22),(0x17ddd96f69554f6abecf57477b15c354ea943a0f4646908cc59ce8e6e7eb95e5b56222212409a74fab4c949ad45d0881030404b6d33b67fdb9fdd6d97bc3b172d2c7bd9691a568a93685a85321144592706c8636706aca1214676df2784a0aa4,0x1014217a0f11054800088220421332448990381e464e92ace78db9b02a0e420b1adc9121a6bd850f230c841ac45d088003040422c01200510008c2000203815408aa084631056aa93485a951311554927373ae00a04a8a1214630512784a0a20),(0x0,0x0),(0xa1d939c4ec3f6a912a8415272be2d391e28f9f4dcd723cc35fe6be4f625743ef914223051440186015739fd9dfdba37efef9ee28a8c69bf021c514dd78c2212ae24535d1b2a82408dbb6ac142aee2bc5f844918460a06a8dd89a687181d9d564,0x540100420204aa5ecc5350f8d20458952218781a9a1284208424448c0718c64a1236ede59401040045313000900a36cf4d1420820400120014514d168802022c64577b1c23a0542cb7a14284eea2845080411264020608dc89068618191c504),(0x0,0x0)]
def pos191 (j : Nat) := (sampleCols191[j]?.getD (0,0)).1
def neg191 (j : Nat) := (sampleCols191[j]?.getD (0,0)).2
def raw191 := rawDecor 191 pos191 neg191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs191 : properPairs (graphGoal 191) (asRow pos191) (asRow neg191) :=
  chart_pairs (m:=191) (p:=pos191) (q:=neg191) (by decide +kernel) (by decide +kernel)
def pk191 : List Packet := [(0xb002fc0000,0x0),(0x8002f40002,0x0),(0x38002f40002,0x0),(0x8002dc0008,0x0),(0x38002dc0008,0x0),(0x8002bc0010,0x0),(0x80027c0020,0x0),(0x380027c0020,0x0),(0x8000fc0080,0x0),(0x38000fc0080,0x0),(0x7002f80001,0x0),(0x7002ec0004,0x0),(0x37002ec0004,0x0),(0x70029c0018,0x0),(0x370007c00a0,0x0),(0x60a28c1000,0x0),(0x160a28c1000,0x1000000000),(0x604a982000,0x0),(0x6408784000,0x0),(0x16408784000,0x10),(0x61206d0000,0x0),(0x5042982001,0x0),(0x5400784001,0x0),(0x50828c1004,0x0),(0x150828c1004,0x1000000000),(0x51006d0004,0x0),(0x5002e40006,0x0),(0x500a982008,0x0),(0x5002d4000a,0x0),(0x5002cc000c,0x0),(0x5002b80011,0x0),(0x500a700022,0x10),(0x50025c0028,0x0),(0x5000f40082,0x0),(0x5010e40084,0x200),(0x5000dc0088,0x0),(0x4002982009,0x0),(0x4002c4000e,0x0),(0x4002b00013,0x0),(0x4002980019,0x0),(0x40006d0024,0x0),(0x4000e40086,0x0)]
def cuts191 := pk191.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert191 : certifiedCuts 191 cuts191 :=
  certifyPackets pastOK187 _ (by decide +kernel)
def layer191_7 : Layer := (61,6,6,4,21,81,6,6,(fun i => 0x60400603307848028551200b0620c0343a028640381a208088212d1381a2081a21818370184e0dc0743a06c1882c250408d074181f01c30410370851901c090c02200001aebaebae99e79657df75955134d34d13eeb6cb2ba89249248a282082081a69a69a69a69a69a6165965944020820011fd19a21678fe94d10abc7f4668855e3fa334424f1fd291e136afa8ccee8b4df5668841a3fa523c26b2fd69a2125e9e93a8a92d5f1e5354963fa523c22b97c7849515eda93a2c8a7ad49916453d6a2c832299dc784d923cde3c28a91e6f1e14544f76ad08a227f951448d13f9ca2a4a81fe64d91440ff622c8a207f993545103fcca2a2681ff44551340fdb26c832071fc8955e22cde3c28b114fd4668840b3eaf00c205bb56845101fd88a20480c5f5668859e37a934426f1dd39a21278fa8cd1093e750e01849e7b2720428d79939021459ec9c810a2de64e4084527b2720422933e99560049db4ca300246f6267701327ab13b8099b5189dc04c9eac24e0266d4612701347ab133009ab51899804d9a8c4aa02477225278cfe328a9aa07f911444d03b96ac809115e94640488a3e91293c23735590121150249a3e610384013c067b948480f6a840f4a0f9340084b3b2c6380f41a8aac3240f7922f300f7877a88e7d39f12bdc40f4c450a124d77afbc0f4f8df680f40f40f5b590b40f40f40f40f40f49c37100f40f40f40f6a6cce1b1c7cd7564e8861c72ab8dd2ed415d2d9f063cabf36de090ba62835148ec3510180f4214000518e12720109604310b0c0040))
def pred191_7 := batchRange 191 raw191 cuts191 7 4 emptyLayer layer191_7 12
theorem cases191_7_0 : pred191_7 0=true := by decide +kernel
theorem cases191_7_12 : pred191_7 12=true := by decide +kernel
theorem cases191_7_24 : pred191_7 24=true := by decide +kernel
theorem cases191_7_36 : pred191_7 36=true := by decide +kernel
theorem cases191_7_48 : pred191_7 48=true := by decide +kernel
theorem cases191_7_60 : pred191_7 60=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved191_7 : settled 191 raw191 7 4 layer191_7 :=
  advanceBatch pairs191 (raw_faithful 191 _ _) cert191 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=6) (by decide +kernel) ⟨cases191_7_0,cases191_7_12,cases191_7_24,cases191_7_36,cases191_7_48,cases191_7_60,True.intro⟩
def layer191_8 : Layer := (297,10,6,3,99,371,7,9,(fun i => (if i<2 then (if i<1 then 0x3fb51444efea2103dfa7740f7e49d03efa6640ff64d903f7a5540fee51503fd93540fee45103fd91340f7b1e222dee7788b7b59e22ded5788b7b4de22ded1788bbb99a22f6e5588beb51622fae4488beb45222fac0488bf38ce22fe90388a7f1e222ded2788a7f5e1129fc7844a7f5e102dec2740b7d9de11df5678477d55e11df5378477d49e11df427847bd99a11f7655847ed51611fb644847ed01211fd633847fc40e11fe622847ed45101bf9388037e9de00df9678037e55e00df9378037e49e00df8278037e45e00efa66803de95600fb945803ee91200fb914803f68ce00fea22803fc84600b3d58012ed46004500f4800da2dee59d463daee904fc04a7b03426808e8e050f34accd6162412571210379551fb6144666b974def075577b443d91e5a7252ae2dc19d83c93255cc66e4659c9ae83ea8202524b20e01b2c3b4a5a95168b92c1647004a71908129dcc8133f00ab2cee476509747e86e1284004a7b4374c56df0c918728f226ec1152467825a45754ab48ec78848389eb804877934be4cb653d0094d05f55d604a4094f8e32837b9e0739ee94740a691e46b669d815b3a1c0948129e9da3be75554b10f4d6c09c829cd180236135104b012971f5d912d73b258789623f9a180ef65cd4718a117e6b704ff3a12f0b4099914004a674ad0ba663b52ff782fd03e0fbcc03e8976d35c753a89e07de6dd5aa28e528ce6671cf360a2f0c6cb2bc18531ad11e0ff99f630cd6611e1a65c0613fa786aa738edab12c7508d20e503abe71b01293dba8b46187e4caccc783f200f791602538236d4c0129ccf4d293a724706d57b036d16f98d0706958a7a902ecc9dae04a4e89e0970252ac4698f188e29c4a966e09cb1a6c2f9a48444171502533968094e11cccee04a4094cd0d0252bac3f06aaa9196804a742b46c73213d452b160129e478d8646056a9a8a1cac7de5701292d4c04a623746b808e1c184094e42102527174094f84c025258b98272204025204a5792d610025204a7b5e04a102525ba03598129025204a49329a4a025204a4094b8315500ca2c09498b571cc9a780949f2702524bcdc6f78c9ac1604a4094ba00447c04a4094f4eeb18004a63840129261604a571586110253f004094ec8165b2d15c0948129025204a4094812902534088094a602f83e2182d65812922146140094febb025204a4094ea3d02531a7cf0e429b0253f40409481297ce2493642456a35c5a801db91705c88d8e8d5520090250859b9685601290253aa27004e05e3927c8a8007568530e461f0c457c3f296c04a4e86424102526fb800056f0000180800c14108240ca8300000a1021c002022400204047852000302000c0030018302020c500002c480021400d162cd881a04286000470902004821e2c18100083800000201044010102000000c04100 else 0x19455114350d424ed3b4d92b48d1d4490940cf73bcee3b0eb3a0e7398e6398dd374dd370d334cd2330ca30cc1304c1304c1300c0300bf2f4bc2e8b92e0b82e0b62d0b0294a12588e2348c21c851ec791c46a18c5c16c5a16057158551545514c53144511444f1083f0e82d09c270982408c220801f07c1f0741d0741d06c1b0541404c110400f0300b0280a028080200601806018030037f0a157bfd6809eff56027dfd5709effa2136dfe774db7f49d36dfd174daffa2126dfe7749b7f4dd26dfd2749b7f45d26efd3649affa2116dfe7745b7f4dd16dfd2745bbf49916bfe8841b7f9dd06dfd3741b7f49d06dfd1741bbf4d906efd1641bef0a145fbc275177f09d45bfe884d77f9dd35dfd274d77f45d35bfe884977f9dd25dfd374977f49d25dfd17497df51525f7d35496ffa2115dfe774577f4dd15dfd274577f09d15f7d25456ffa2105dfe774177f4dd05dfd274177f09d05dfd17417df45505fbd36453ef49914fbd06453ef4d514fbd25453ef41514ff516452ffa2123bfd6848eff56123dfe7748f7f59d23dfd5748f7f49d23dfd1748ff74d923fbd4548fef45123bfe8844eff5a113bfd5844f7f9dd13dfd6744f7f55d13dfd2744fef51513ff51544ff748d13ff92640ffe45903ff92540ffe45503bfd6840eff56103fdd3640ffe41903fdd3540ffe41503fdd1340f7f9de22dfd5788b7f45e22fbd4588bef45222bfe8844b7f5e112bfd6844aff56112bfd3844b7f9dd12dfd6744b7f55d12dfd3744b7f49d12ff51644bef51512ff51344bfe40d12bfe8840b7f1e102bfd6840aff56102bfd3840bfd06102dfe7740b7f59d02dfd5740b7f4dd02dfd2740b7f45d02ff90640bef51502fed2540bef45102ff90340bfb44902bfd6800aff56002bfd68406ff56101bfd38406ff4a101dfd674077f55d01dfd374077f49d01fbd45407fd45501ff903407fe409019fd689de7f56277dbd489de7f4e2779fd289de7f462779fe8859e7fa21579fe884de7fa2127ddc3849f7d061279fd6809e7f560279fd3809e7f46027ded2709e7fa2117cfe7799b3f4de66cfd2799b3f09e66cfd1799afe021469fd784da7f1e136cfd674da7f5e1269fc7849a7f5e1169fc7845b5f9de55d7d379575f49e55d7c279575f45e55bbe88517ee02145dbe775176f49d45bf8085167f5e1359fc784d7cf515359fd784967f1e125f3d454967f5e1159fc78457cf51505dbe779136f59e44dbd579136f49e44dbc279136f45e44ebe66913cf956449fc78492fe02124dec27492efa2114bbd58453ee02114dbe774536f49d14ebe66453ed45914f3e55452fe02114bbd58012ef46004dbe770136f49c04ebe66013cf95404dde778cf7759e33ddd578cf7749e33ddc278cf7745e33ede668cfd795633f9d458cfe7452339fd7848e7f1e1239fd7844e7f1e11) else (if i<3 then 0x4544e9a376910dc06910a0d0ed2222806dd079819bb4691559010d5a456adda4e690cd8d0ad218d0ad218d0b09f9b844074e844034c103883f6a4130e20fe7426a4181a2cc0b3a4434c4b1c5cf1034f4717212c30d301e58a54dd52a9a6cd079ab5bc51ede2b78a89a458addbc136de0b4822c785453cd8e983df8f1cfd5166f35b963419b964419d2f2c1a69655145b7546c5b7542d7aa163c38b6ea83222e60db7742de9a36f43b70c3d7981c2c3224668dba6e58d372cbcb4b6e58585362c28b0a2c785786de1a78187889618b8844c8ca968355052c85bbb34c90a968355052c64f37721072132a55052c3579368adda17265a0d0a594b78a19da172654b41aa8b056f38545049d9996ed06c05415e026684fb768355057809da17265a3028f954e0ab813b42e4cb41b15b85784d42018dc5284055bc26465b9668350a60aa5da16e59a0d32154b272790995e586930ab94b482ed0b932dcb341a1454d5301f027685c996ed06cd542de03063c383060d99954d02c532506aa0a594b39a34dbb625204b32d06b70aed9c56665a0d429e6852ca59996835baa8acccb41b3d50b0a59483063c383060c10232cc7b73ef213342a9a058a84a0d5414b29667e69948e88426251eb342d06b70b159a16834c9f9a14b292c64ea748e88b17acd0b41add5218ad06aa0a5949f67385963291d1178c6583360c18f0e0c18342646810a0183730094916e7993a842de020a3dbc216f01082cb02896445002103c19b060c383060cd830e0d099681623b42e4c8d2814b299884cb4550dda1726662a0a5948b0a261ad2108a4b04086b08451f8220996351a4a1205cfd902212dc106d0991e28c96351a7973f96e08368450535583492e14fc203360c183066c187063c1c57685c9968355852ca66bf1e1c1a132d1b8d82ed0b932d068b0a594cf9884c8d0add783360c1831e0c19b063c1960ab48bc963819b060c18f0e0c183360c38322b94915ca4522713094482311084401f0f074381b0d06430170b05428130924423100803e1c8e074351a0d86230180b05626128904d2110480461e0e8703c190c46034150a05c24110804c1c0d064301e0a048201405024100f0280c040101c0143d8f63d6f4fd3f47cef23c5f0fc1effbbee7b5ecfb1ebbaaea3a5e879ee6796e4b8fe338ae1f85e0f7ddef79ddb72db769d9b64d875fd7759d5f54d474ed3347d1743d073ecf33ace334ccb30cbb2cca326c8b20c771bc6717c5312c3309c1b01bf6f7bd2f0bb6eaba2e4b82ddb6ad6b4ad0b32c6b12c3b06bfaf2baae6b7ad2b2ac2adaaea9a9aa4a8e9fa7299a6294a3e8ca2e87a0e809f67a9de749be6c9a66498e6197a5b966569525193e4d92647916418fa32896248660d7f9f37a5dc745cc719bb6c1a665d9762d8a62586615846117f5d56e59d5c5594b529495 else 0x11263479d3768dd0b46929d8d0efda4a1adddbb6ed24a7423c3b79239d8f7edddbb6ed24056f207850c210966e590bb3e9d09f4e847873e9d09f1c94f8f0c7c39a2c71d1f54e5bb768d1bb48e343c27ed23b772ddca76938ca73e647874ede6994e58ca71cfdbb92ce5bb48d187856ea9c864ce8c966e58cb93e64f991e1de17307cc86753440f0c20f089a2130610e843a2c15bb46915a))))
def pred191_8 := batchRange 191 raw191 cuts191 8 3 layer191_7 layer191_8 12
theorem cases191_8_0 : pred191_8 0=true := by decide +kernel
theorem cases191_8_12 : pred191_8 12=true := by decide +kernel
theorem cases191_8_24 : pred191_8 24=true := by decide +kernel
theorem cases191_8_36 : pred191_8 36=true := by decide +kernel
theorem cases191_8_48 : pred191_8 48=true := by decide +kernel
theorem cases191_8_60 : pred191_8 60=true := by decide +kernel
theorem cases191_8_72 : pred191_8 72=true := by decide +kernel
theorem cases191_8_84 : pred191_8 84=true := by decide +kernel
theorem cases191_8_96 : pred191_8 96=true := by decide +kernel
theorem cases191_8_108 : pred191_8 108=true := by decide +kernel
theorem cases191_8_120 : pred191_8 120=true := by decide +kernel
theorem cases191_8_132 : pred191_8 132=true := by decide +kernel
theorem cases191_8_144 : pred191_8 144=true := by decide +kernel
theorem cases191_8_156 : pred191_8 156=true := by decide +kernel
theorem cases191_8_168 : pred191_8 168=true := by decide +kernel
theorem cases191_8_180 : pred191_8 180=true := by decide +kernel
theorem cases191_8_192 : pred191_8 192=true := by decide +kernel
theorem cases191_8_204 : pred191_8 204=true := by decide +kernel
theorem cases191_8_216 : pred191_8 216=true := by decide +kernel
theorem cases191_8_228 : pred191_8 228=true := by decide +kernel
theorem cases191_8_240 : pred191_8 240=true := by decide +kernel
theorem cases191_8_252 : pred191_8 252=true := by decide +kernel
theorem cases191_8_264 : pred191_8 264=true := by decide +kernel
theorem cases191_8_276 : pred191_8 276=true := by decide +kernel
theorem cases191_8_288 : pred191_8 288=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved191_8 : settled 191 raw191 8 3 layer191_8 :=
  advanceBatch pairs191 (raw_faithful 191 _ _) cert191 solved191_7 (width:=12) (groupsN:=25) (by decide +kernel) ⟨cases191_8_0,cases191_8_12,cases191_8_24,cases191_8_36,cases191_8_48,cases191_8_60,cases191_8_72,cases191_8_84,cases191_8_96,cases191_8_108,cases191_8_120,cases191_8_132,cases191_8_144,cases191_8_156,cases191_8_168,cases191_8_180,cases191_8_192,cases191_8_204,cases191_8_216,cases191_8_228,cases191_8_240,cases191_8_252,cases191_8_264,cases191_8_276,cases191_8_288,True.intro⟩
def layer191_9 : Layer := (46,10,6,2,16,57,5,6,(fun i => 0x143d821a0cd31748bb4686a44f21a0d65122e819d86a5086837573cb19186a50f6835d22261a12943ca2050d748b68686a50f875203318b685d298b686d2750f21a5d22f40e116a3c86836164d02681257616df872b4f31a0d8a964d01e61126dd2a4c6d3e13080d8593409644764c2d3e1308698593409a0249d1513cc21a0d3409a0495675421a0d854e24445d94b84631b7e1bed50c6836153879847516ca8b6b565213080d854e25911d462bad52384c21a61538909d44550c21a0d538911d46550f2880d855025912131b9543c869855027408b84331b1657e1b2d50f3036154076446ca7e1aed50f31a6154079826ca1543cc6835501e611749b34a2271b3b543cc203628550989699127a6d50f84c21855025908550f84c2050d540964495850f84ccc8d0355025a64496750f308695409d029453543cc21a0d5409b44958cc04ce62a1d9b4231e5d272104dccbd0694e1d909651d49c8413732e81a54c764275744f72104dccb1a54ce65f09e5d26c134a2261a54ce1c279749c8413732da1a54ce1c23187a85d27013662d9d06b5338767479749c8413732c50e50014d640911d34004e45524474d60e26175744fccb1a50013185502446d8261d027974b32c50e53096d80011ca55010d6cc807a9e5d235b20a9c600165540910d00108555024d00135831540910a09c98908c8884807c7874706c6864605c54504c4844403e383a3434302c2a24262120221c1e19181a141610120d0c0e080a0504070101800de90a067399e5c93e3d8c622839fe7b1de735bb6a9996357e5b55d531394a51b438fd3c4e2330bb2ac9b22c7819c5e15449100330bc260641102400ffcefff59ffeabffd37ffa4fff09ffe8bffd46ffa6dff49bfe8b7fd06ffa8bff4d7fe92ffd15ffa0bff493fe8a7fd23ffa27ff40fff117fd12ffa05ff00bfe80ffe00bfcef7f59efeabdfd37bfa4f7f09efe8befe66efcabef517df227bd14f7809f78cffc81fee22fec23fe80140a6589309802e02ebc626720fe9f3812ebb264570a218b2d002e1e418a3ac02e5edd9c58c51128da964da02e36902ef44121123dc502e3021d9668ec860085e02e8201d4a8902ec8ef0302e02ed6a5d5cc7e1b15d79210980006206848500140))
def pred191_9 := batchRange 191 raw191 cuts191 9 2 layer191_8 layer191_9 12
theorem cases191_9_0 : pred191_9 0=true := by decide +kernel
theorem cases191_9_12 : pred191_9 12=true := by decide +kernel
theorem cases191_9_24 : pred191_9 24=true := by decide +kernel
theorem cases191_9_36 : pred191_9 36=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved191_9 : settled 191 raw191 9 2 layer191_9 :=
  advanceBatch pairs191 (raw_faithful 191 _ _) cert191 solved191_8 (width:=12) (groupsN:=4) (by decide +kernel) ⟨cases191_9_0,cases191_9_12,cases191_9_24,cases191_9_36,True.intro⟩
def layer191_10 : Layer := (1,4,6,0,1,2,0,1,(fun i => 0x818304e24734510200000b0ff500a01))
def pred191_10 := batchRange 191 raw191 cuts191 10 1 layer191_9 layer191_10 12
theorem cases191_10_0 : pred191_10 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved191_10 : settled 191 raw191 10 1 layer191_10 :=
  advanceBatch pairs191 (raw_faithful 191 _ _) cert191 solved191_9 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases191_10_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra191 : Lower (roots 191 true) (graphGoal 191) 11 := by
  apply finishAug (cap:=10) 0x20000201020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=191) (l:=11); decide +kernel)
  have eq : (nodeValues raw191 1 (nodeBits layer191_10 1 raw191.length 0)).toFinset = (roots 191 true).toFinset := by decide +kernel
  exact eq ▸ solved191_10 0 (by decide +kernel)
def past191 : List (Nat × Nat) := (191,11)::past187
theorem pastOK191 : AugKnown past191 := augExtend extra191 pastOK187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra255 : Lower (roots 255 true) (graphGoal 255) 12 := by
  exact dropLower (q:=191) (extra:=true) (s:=64) (hints:=0x80000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra191 (by decide +kernel) (by decide +kernel)
def past255 : List (Nat × Nat) := (255,12)::past191
theorem pastOK255 : AugKnown past255 := augExtend extra255 pastOK191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra347 : Lower (roots 347 true) (graphGoal 347) 8 := by
  exact lower_map (ms:=([81,82,101,118,135] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra189
def past347 : List (Nat × Nat) := (347,8)::past255
theorem pastOK347 : AugKnown past347 := augExtend extra347 pastOK255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra95 : Lower (roots 95 true) (graphGoal 95) 8 := by
  exact dropLower (q:=31) (extra:=true) (s:=64) (hints:=0x80000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra31 (by decide +kernel) (by decide +kernel)
def past95 : List (Nat × Nat) := (95,8)::past347
theorem pastOK95 : AugKnown past95 := augExtend extra95 pastOK347
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra127 : Lower (roots 127 true) (graphGoal 127) 9 := by
  exact dropLower (q:=95) (extra:=true) (s:=32) (hints:=0x200000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra95 (by decide +kernel) (by decide +kernel)
def past127 : List (Nat × Nat) := (127,9)::past95
theorem pastOK127 : AugKnown past127 := augExtend extra127 pastOK95
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra313 : Lower (roots 313 true) (graphGoal 313) 7 := by
  exact lower_map (ms:=([81,98,118,135] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra31
def past313 : List (Nat × Nat) := (313,7)::past127
theorem pastOK313 : AugKnown past313 := augExtend extra313 pastOK127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra317 : Lower (roots 317 true) (graphGoal 317) 8 := by
  exact dropLower (q:=313) (extra:=true) (s:=4) (hints:=0x200000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra313 (by decide +kernel) (by decide +kernel)
def past317 : List (Nat × Nat) := (317,8)::past313
theorem pastOK317 : AugKnown past317 := augExtend extra317 pastOK313
def sampleCols319 : Array (Bits × Bits) := #[(0xf93b9a06eab33f7e0f9d761b4a43ba4fc82eb13dba6b7e351ab5dd377ec0ce24e114a0522b6cabc3979512f3414b4c66d0c87b7771cc4c29c32e6dbc32d1621c307ca8eb6f83d64c0641c4e71ec088868b5590b950d0c5853b23fc321e01c68,0x4010080400000a0e102584254014a8102024340002284324408510c238ac740c8082220200c002800214001000410842c0800222118c0809000a051802402018204c2860a90432480010000396802080005188a1f81001841a203c101400c68),(0xf4bf0ffea24ffa1f721faae397e0f2dc160c7eb7db8d0cac5af5b9f21d78554519b12250005371e78dcd193c60a3c199b4f3ed3d12b07879cec78dc68e124fd22e4d7054b4364918758c5642d921c5e73adb09418420fe41ad0371aa57aba011,0x51100e0a0242aa0114898094a2a0a4701cd438b89d5c61cc02e588724c40203105b30407dfd050c1044c190c2020c00880e3e11c10801009444305820600419044c1147075671c58711c76e1c401c5a338d803048020be418801702a16a38011),(0xc86fb1dfaedac81633376e9f07a84659498fb585e97cce3c4d52fce63362640effa821d008412b3bb4952d682bd89a055d366e698b4b8bbe72f18b7032fef927bb5e6854ce25409025ab4202285a517e562f40d8e813720e770c4259671c31a3,0x8c4d30108988402623303703104e408e6008810160a19a207d1a3684b0b454ce3a4cfbf8202c22089091202001d012015d140e218241831412b00a4010602827b91e69878888418086a1001608fe105c4323e0ba6003400e770c0051611c31a0),(0xbbfcf7b79dc61781210958dde87fc6e11b7fd8d87c399596ab77364cabca233fbb4e05aa580091980e9ebe9f806c116093d71b6268a73785b14c65267ddda75d86e1bd355f93848d1abb0411a312961a848c1f146afaa887406182b514d5461e,0x4000090100460141c00d487066002a411a426260081a059b008041400b0b0b0041020006885011900a00041a002801600002014040800000204c44244018050806c1840846178c16401a0401a1010002808418001fb82881000082a404c1060a),(0x88914207f7be1fe85191d2537a7ead7cf4c65978e56b7ae61d7b0a8ab9563db75e4448025286c4c3f3667080b2f15e3b469c509385d2b62b2f2570bcfd22f97d49cfacb1916a806d9ba0587e86469c245a3c292cb0e4952c30d098707226b3dd,0x22c00244a4815c001a30a68981ec943c44ac9899f5457a441b77aeb3947430af36f5ddd957a28042b1061080b2010e1200945011040226230a2110802902b044591a3871b16820c93fa4db7e441694755a7a6524a0449524305018107226b195),(0x5025da2ed4d03e7b8e6125102220a4721cc679f8fd77ff7b5f9ef7b5d6bdd2c820009005a529bf5ffb41cac4cf4fef7f68493a4cf6c8410541db1ead40e1a0d01051061a1523365e51e8f7f365cf301d4363f0a2015d03f28e0c84209ea7bda0,0x2084361c0092501009a61022382468d8c130b45f1d51c890d724629c2010813327189799f189176b400a04884aa95b40010a081240000401000a2c40818054245b04181523b45258aa47dbc4851512b2f2c020405c02e20e0484201ea5b080),(0x0,0x0),(0x0,0x0),(0xbf404649117de9899f28f4c3d0cd4acf527c9a398d70616aaf9e92b49eddf2e92d0294288508144042b2c6f3df2f6fdeaae3e19e9977bffe9eb89b43120008a95434b9c5aa9a438a1518f5e10443320dc369b7a6820241b188ff7055e943c1b1,0xab0860404119040c2370108398c4c194050c8d0ba060aa244f289a9420d4646e0cd8e768660c04000090c0e0460544042240208689363dea8c90810212000823d9047bc5a88843a90500b820104ac2ad4909279ea002411080fb7051e1024131)]
def pos319 (j : Nat) := (sampleCols319[j]?.getD (0,0)).1
def neg319 (j : Nat) := (sampleCols319[j]?.getD (0,0)).2
def raw319 := rawDecor 319 pos319 neg319
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs319 : properPairs (graphGoal 319) (asRow pos319) (asRow neg319) :=
  chart_pairs (m:=319) (p:=pos319) (q:=neg319) (by decide +kernel) (by decide +kernel)
def pk319 : List Packet := [(0xb004fc0000,0x0),(0x8004f40002,0x0),(0x38004f40002,0x0),(0x8014e40004,0x200),(0x38014e40004,0x200),(0x88007c0020,0x8000000000000000000),(0x388007c0020,0x8000000000000000000),(0x8000fc0100,0x0),(0x38000fc0100,0x0),(0x7004f80001,0x0),(0x37004e40006,0x0),(0x370007c0120,0x0),(0x602ce00400,0x0),(0x1602ce00400,0x10),(0x6054c40800,0x0),(0x6808784000,0x0),(0x16808784000,0x10),(0x61405e0000,0x0),(0x6034c40008,0x80200),(0x6014b40010,0x200),(0x5024e00401,0x0),(0x5800784001,0x0),(0x5044c40802,0x0),(0x5004f00003,0x0),(0x1500ce00404,0x10),(0x5014c40808,0x0),(0x51005e0008,0x0),(0x5014c4000c,0x200),(0x5004b40012,0x0),(0x58009c0018,0x20000000000000000000),(0x50405e0020,0x0),(0x5004780021,0x0),(0x5024640022,0x200000),(0x5014640024,0x200),(0x58003c0030,0x8000000000000000000),(0x15008784100,0x10),(0x5000f40102,0x0),(0x5010e40104,0x200),(0x5000dc0108,0x0),(0x5000bc0110,0x0),(0x4004e00405,0x0),(0x4004c4080a,0x0),(0x40005e0028,0x0),(0x4000784101,0x0)]
def cuts319 := pk319.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert319 : certifiedCuts 319 cuts319 :=
  certifyPackets pastOK317 _ (by decide +kernel)
def layer319_5 : Layer := (3,0,6,0,1,9,0,2,(fun i => 0x4f111b229454d5038370f6452b28a2073c456c8a4511340d400303ba03a0030303a9))
def pred319_5 := batchRange 319 raw319 cuts319 5 6 emptyLayer layer319_5 12
theorem cases319_5_0 : pred319_5 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_5 : settled 319 raw319 5 6 layer319_5 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases319_5_0,True.intro⟩
def layer319_6 : Layer := (65,5,6,5,22,81,6,7,(fun i => 0x22222222233333a220c9aa1a201402a0520880e81c02682484d88b0880015ce739ce6f59c5ed5a4e739460f7bdee6b14a529284210839cc52084108400000000000000000000000647ad2ac06802665a52ac06802656ad28c06802674a528c06802537295440f081ec72d2ac89081ed32d29c89081ee32b29c89081ee52b29489081ef12729489081ed62d28c89081ee62b28c89081ef22728c89081ef42528c89081ea72b23c09081eb62323c09081da72b4242ce81db6234242ce81da72b42424e81db62342424e81ceb2b41ca4c81cf32941ca4c81cfa2341ca4c81cf623444a8a81f272b43c28a81ce7134ac28a81f270f0ac28a81df22342426a81de3114a2a6a81fa30f0a2a6a81fa324ea2a6a81eab0f29aa2a81dd32d42426881de32b42426881df12542426881df22342426881ce72b444a2881c77114aca2881f362343c22881e372b23c22881cf61348c22881f360f08c22881de32b42422681dba0f48aa2681df21148a22681fb20f08a22681fb22ce8a22681c37a954caf081e47ad2ac89081e53ad29c89081e65ab29489081e71a729489081e56ad28c89081e66ab28c89081e74a528c89081e672b28489081e762328489081e27ab23c09081e36a323c09081d36a34242ce81d27ab42424e81f270f0a2a0a81eb60f28a20680e272b23c09081e362323c09081a814054cbded0082939f0cc26965e8a3b155ea5c7e096020e480082002713881901852c4024e1c082791c98fcd9a15f2e55936b7d1cd26f0f10cf931328c0456e131332b747f470082624020810671a5babdf2e75380d15d1e2adc082041020d849b36041605d0873200410208104826335a0a42ede03d1fec070f7a44083e580104a4a041ac210800008409800b06801700300a002))
def pred319_6 := batchRange 319 raw319 cuts319 6 5 layer319_5 layer319_6 12
theorem cases319_6_0 : pred319_6 0=true := by decide +kernel
theorem cases319_6_12 : pred319_6 12=true := by decide +kernel
theorem cases319_6_24 : pred319_6 24=true := by decide +kernel
theorem cases319_6_36 : pred319_6 36=true := by decide +kernel
theorem cases319_6_48 : pred319_6 48=true := by decide +kernel
theorem cases319_6_60 : pred319_6 60=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_6 : settled 319 raw319 6 5 layer319_6 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 solved319_5 (width:=12) (groupsN:=6) (by decide +kernel) ⟨cases319_6_0,cases319_6_12,cases319_6_24,cases319_6_36,cases319_6_48,cases319_6_60,True.intro⟩
def layer319_7 : Layer := (377,8,6,4,126,473,7,9,(fun i => (if i<2 then (if i<1 then 0xbd28c8091157a1e50388afa272024237355901211af83ca0708a8028e472db2c4000e0ca0667b8a4c1c70da00bc8179d51805e40bcb67902f3c996a8872c902f2a4ea76e817902f205e40bc8a46e5bc5087256f131141605e59b48179d4f6fb66d22d23f70392153fa326f3ea2205e40bc8a198a8405e6768017981b7f2580bce74fada405e458b6adf6d8a05e40bca0bc02f3e4e4da21ca702f339d3d7cb504b9fd6500142017902f205e72a60179c4df819ec76381f02f205e61273e0d02f369200bc817902f3909c0bcb0ed02f205e750a254a30dd85b0b1a029a5a444246a0064e602f23be0d45017930da9221a4a22f13d26da780bce50f5a40a875fa1bb78adc24baba535c152d4762d806464121ee8f962e7d88b885af914709a92c2043005e773638806c6bc3bff8d820ccce41c0205f03751e5b49fd82924d1662405e660181797ae260c523ab84489ad4333f700d1a76435c96aad38995cb23191c2eaf577c12c39c0bce52fccb475dcf0d8e02809920979541e78e90d9d2f750b6cd79c45af4d121ea2caa23bf4546db0ad5b97c6469b5d61c478e3f37251c53254078aefb9bd373def94a7c2a9e5066903842034a632c18005e451c2e2802f205e40bc8179cecf197cb868179cc7dd15f75d06067c8f53a1993c08316781a6086c4633e68b65800bc9c6bc53e8a6f330690cd65c05e7e54bc1102f2dac34008179c572d10000bc28779259c140bcd513becb0a140bcd422e56a05e76bb507cd63f61f80bcad6df9e40c9ae57017902f36cec0bc8a0f02f2aaa80bc8179296405e6517e13fcec704afe218179dc6f63ba838bafa02f205e55acf90b02f2803b0028179c6bd693fc10561302f2cd700bcc049d4e78b07a83d65e9d9405e5155871d7ab6c45688c02da26a84109aac0179b4ccb8b605a609c02f343d812b112a02f2542104b817989038105c748179881432ddb9ef8c30666e9e820401798c9705480bc817928e110a87b300896d2005e533e817902f2f57c0bccf3896dce39079181798e0489a9d30817902f2f45c0bcda8ead3a045009a7c2e205850a441b01798e61bdab1a6b0c671aa6a96ca3d2d42cd1b93697a0506c034e1de031928b3293854f48f303dce062d7693b1564d02c23d6e11a4cb99d605e6fb9634e02f31dc335f817902f220980bc81796eac801248778b3027d4a574184e3bd648faef27829099dfebcb3d1d3d5512822170f6712b101a6fb946560179caa15a3d9579f6bcade4a092316a1e02f3458948e1cc74665540451306242130204064060000f001029500c82830408784000421648281860199886680c6832a1009210000000000184029800c0e007010a0000100202840068200062418200082021e088010630000102c2000044402001408610000830a742160200410000401118041860400180 else 0xcac89081dfa4a44840efe232242075f8794a103bdc24a5081d7e1e51840ef70928c2079f87846103bec9ccee81e7e1e27740ebf112b3a07db84859d039fc44ace81cfe2255740f3f0f0aba079f8784dd03afc44a4e81f6e1212740e7f11293a073f88945d03cfc3c22e81df60e52640ef7112a2a07db87851503ddc3c28a81fce5614540fb724ea2a07dd8784d503fcc2426a81f7649d3540feb28a9aa07f39454d503fac9aa4a81d7e1e51540f3f0f08aa07f593545503bec1cc8881df65653440fbb0f09a207f98484d103eecb3a6881f7649d3440ff328c9a207f99454d103b7cb486881dde5643440efd2521a2077f1190d103fcc9a24881dee2251440ef72b28a207db87845103ddc3c22881fec4611440fb72ce8a207f993545103fcc9a22881df65651340efb29289a07dd87844d03fcc2422681f7659d1340ffa22c89a07f994544d03fe88aa2681ff44511340ff622889a073bd49a21038ff4caf081c7fa647840eb78923c2073bc491e1038fe3cad081cef1256840e3f8f2ac2073bc4956103d5eb489081ecf5644840f73a7224207bad2912103dda8c89081eee4244840ee7ab2242077b51912103cde3c09081cbf5a44840e6fab2242073ed29121039fa8c89081cfe4244840ebba733ba079bc489dd038fe44ace81e6f1216740e3f912aba079bc4855d03cde2426e81d7e4243740e3f91293a079bc4849d038fe44a2e81e6f1211740e77912a2a079bc7851503cfc3c20a81fce5150540e779128a2079bc7845103b7cb480881dde5640440efb272022077e92901103bf88c80881c7f6267700e7ea33442051fc795a1028fe3cab08147f1e53840a778929c2051fc795a1018fe3cab080c7f1e538406778929c203db56745101eda1ba2880d7e1e503407f622881a031fd790e2009beac871004ef524388027ea321c4013f9090e2008fe44a4f0057e1e5038022fab21c4ef1f5190e2778beacd10b3c6f526884de1fad22406f17d59120378f6948901bc7d464480de3f2122406f1f519a21278ee1caf0935e64e4085167b2720428b1bc894de44bcc9c8108a4f64e4084523f0f344009a7968560049ed4ca70026b65a1380136b2b09c009bc9384a004de89c230026f84a1180123f3133b8099d9389dc04d6c9c4cc026d64e255013732712200933e99560049db4ca300246f6267701327ab13b8099b5189dc04c9eac2ce0266d4616701327ab01b8099b5180dc04c9eac24e0266d4612701347ab133009ab51899804d9a8c4aa025c7564048cef2a32024671fa991e103b9cac89081dec4644840f370f0242071f88959d038fc44a4e81e3e1e26640f2f0f12aa079b87851503f8ca2a6a81e6e1e24440e7b1129a2079d8784d103cdc3c22881e761e23340ff222889a071bc491e10399eac89081ced4644840ef92720244572d5901222) else (if i<3 then 0x261615f5e5e5e5e5c5b5b5a595958565655555555555555555555545453515050504f4e4c4b4b48474646434241403f3e3d3d3d3d3d3c3c3c3c3b3a3a3a3939393938383736353535353532322f2f2c2c292929292929292929292929292929292929292929292929292929292929292929292928272623201d1c1b181514141411100d0a0602020202010101008fe848713bd5f564389debea321c4ef9dd380e2779beac8713bcfd464389df77290844ef37d59a21678fe9cd10abe6f526884de3fa934426f5bd49a2137aee9ccee9bc7f424480de3fa134424f3f519a21278fe9cd108bcdf5643851a7da521c28d3f5190e14697e44a8c9b4f70e57849a3fa723c24d1fd790e1269beac870934ef5243849a7ea321c24d3f9090e1268fe9c8f08b47f5e43845a6fab21c22d3bd490e1169fc848708b4df5668841af6a321c28b7b9090e145ade9486ea2cfd464385165fad34426bd3d27515359be44a8a9ac7f4e4784963faf21c24b3bd490e1259fa8c87092cfe424384972f8f09aa4b1fd391e1158febc8708acef524384567f2121c22b97c784d515e9e1ba8a82f4f49d454163f8f29c4893f9090e2448fe44a6f225774e6774d23f8f344069a7d6856034d76b42501a6db561280d35ead08c069b755846034df2942301a6be5a1080d36f2b084069be92842034df88c2101a47f626770d31fad13b86997d589dc34cf6944ee1a67d462770d31fad0ab8699ed2855c34cfa8c2ae1a63f5a1370d32fab09b8699ed284dc34cfa8c26e1a63f5a1170d32fab08b8699ed2845c34d5eb428a1a6eb4a1450d376a30a28693f909a21249ee1cad0924bf5a4384926fab21c2493f5190e124b9eac8708a5ee42438452b7ad21ba299bd580dd14ade3ca6c8a56f1e5354526fab21c2296bd690d114b9eac8688a5eb4a4344523fb133b8098fd689dc04cbeac4ee026774e2770133da513b8099f5189dc04cbeac2ce026774e1670133da50b38099f51859c04c7eb426e0265f561370133ba709b8099ed284dc04cfa8c26e0263f5a1270132fab0938099dd3849c04cfa8c24e026cf5614601373a70a3009bb51851804b5eb4868025eb4a43401367ab01a009bb5180d004d9eac248026e74e12401376a30920091fe991e2338fe3cad119c7f1e5588ce3f8f2944671fc79462338fe3ca1119c7f225578ce3f9129bc671fc8945e338fe3cad091c7f1e55848f378f0a2a473ec89491239f694d1089c7f1e56844e3f8f2ac2275f47945913cde3c28a89d7d1e51544fb6ace8a2273f48945113bdca4d1081e7ea647840f3f2b23c2079f9191e103cfd440f081dee1247840ebf0f2b42077b8495a103afc3cab081dee1255840f3f0f0ac207eb96912103f9cac89081dee5644840ff327224207fa92912103fd88c89081dee4644840fb70f0242076f96912103bb else 0x1ba1ab5ab534d0e596ad6ad718b4001a79e4924802082082114924871c7196596aaf9b030c31b3c5e0f72eb8462e56e62ebaedabbaebb39eebaeb8eb8abae39dd34615d3438ab76d955f956be58e5aaedbadb6db736ab9f328de2b2a7e279cee00aa6b29ab0c2fbc0bb74aebaec87b92aa67501ea99dbaebaeba8966140b4b775cdedb17aedb3b64841ae7daecf48f8d398020b657952b882cf82822677dcb84ab7d049b4c840c30a82908c220781d070180581505013048112401003c0e2340d0330ba2c8bc2a8a22a898250922409c228862287a1886c168521405c12846128300e8220b01a0481007c0d02c0700006003ae1e1e1e1e1e1e1e1e1e1e1e1e0dfdededededededededededddddcdcdbdbdbdbdad9d9d8d7d7d7d7d4d4d4d4d3d3d2d2d2d2d1d0cecececdcccccbcacacacacacacacacacacacac9c9c8c8c8c8c8c8c8c8c8c8c8c8c7c6c5c4c4c4c4c4c3c2c2c2c2c2c2c1c0bfbfbfbfbfbfbfbebdbcbbbbbbbbbbbbbab9b8b7b6b5b4b4b4b2b0afaeadadadadadadadadadadadadadadadadadadadaba8a8a8a7a6a5a5a4a3a2a1a09e9d9c9a999897959594939291908f8e8d8b8b8a898887868686858483828281807f7e7d7c7b7a7979777776767574747373737373737271706f6f6e6b6a69686766666666656463636))))
def pred319_7 := batchRange 319 raw319 cuts319 7 4 layer319_6 layer319_7 12
theorem cases319_7_0 : pred319_7 0=true := by decide +kernel
theorem cases319_7_12 : pred319_7 12=true := by decide +kernel
theorem cases319_7_24 : pred319_7 24=true := by decide +kernel
theorem cases319_7_36 : pred319_7 36=true := by decide +kernel
theorem cases319_7_48 : pred319_7 48=true := by decide +kernel
theorem cases319_7_60 : pred319_7 60=true := by decide +kernel
theorem cases319_7_72 : pred319_7 72=true := by decide +kernel
theorem cases319_7_84 : pred319_7 84=true := by decide +kernel
theorem cases319_7_96 : pred319_7 96=true := by decide +kernel
theorem cases319_7_108 : pred319_7 108=true := by decide +kernel
theorem cases319_7_120 : pred319_7 120=true := by decide +kernel
theorem cases319_7_132 : pred319_7 132=true := by decide +kernel
theorem cases319_7_144 : pred319_7 144=true := by decide +kernel
theorem cases319_7_156 : pred319_7 156=true := by decide +kernel
theorem cases319_7_168 : pred319_7 168=true := by decide +kernel
theorem cases319_7_180 : pred319_7 180=true := by decide +kernel
theorem cases319_7_192 : pred319_7 192=true := by decide +kernel
theorem cases319_7_204 : pred319_7 204=true := by decide +kernel
theorem cases319_7_216 : pred319_7 216=true := by decide +kernel
theorem cases319_7_228 : pred319_7 228=true := by decide +kernel
theorem cases319_7_240 : pred319_7 240=true := by decide +kernel
theorem cases319_7_252 : pred319_7 252=true := by decide +kernel
theorem cases319_7_264 : pred319_7 264=true := by decide +kernel
theorem cases319_7_276 : pred319_7 276=true := by decide +kernel
theorem cases319_7_288 : pred319_7 288=true := by decide +kernel
theorem cases319_7_300 : pred319_7 300=true := by decide +kernel
theorem cases319_7_312 : pred319_7 312=true := by decide +kernel
theorem cases319_7_324 : pred319_7 324=true := by decide +kernel
theorem cases319_7_336 : pred319_7 336=true := by decide +kernel
theorem cases319_7_348 : pred319_7 348=true := by decide +kernel
theorem cases319_7_360 : pred319_7 360=true := by decide +kernel
theorem cases319_7_372 : pred319_7 372=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_7 : settled 319 raw319 7 4 layer319_7 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 solved319_6 (width:=12) (groupsN:=32) (by decide +kernel) ⟨cases319_7_0,cases319_7_12,cases319_7_24,cases319_7_36,cases319_7_48,cases319_7_60,cases319_7_72,cases319_7_84,cases319_7_96,cases319_7_108,cases319_7_120,cases319_7_132,cases319_7_144,cases319_7_156,cases319_7_168,cases319_7_180,cases319_7_192,cases319_7_204,cases319_7_216,cases319_7_228,cases319_7_240,cases319_7_252,cases319_7_264,cases319_7_276,cases319_7_288,cases319_7_300,cases319_7_312,cases319_7_324,cases319_7_336,cases319_7_348,cases319_7_360,cases319_7_372,True.intro⟩
def layer319_8 : Layer := (593,11,6,3,198,745,7,10,(fun i => (if i<3 then (if i<1 then 0x300946f81409440945639b24e38660094409462440094741d5f18e725009440944094465b5d3fd15979249f6f7c2280944094640e4a72c0946605613de04a8a2b5716298d9955be1ff914ec66a9100d207c91d98ae43f3a495b25e7849c3cf443967680947e73043e409440947a8a9a0b4719d644e57340947a52f07c061808675061009441648e46b717131a444f1a06b96521881009134ea2224108038cde3c2a69d96cc0944e29d03d985a40944094567cad0fc094409440944094409467234201248b8528f73173535e1240945e0b242ffd3b40947f460094409454219588ff5f245c0c544b2d403ac4706e90de6a80946b6c80946d59b962e814009469830d6d80945c0340944760c094722bb0027a1c0c3640618094411f2863d550ce0e1c87eb35f2473c10c374e555c0944094632a988fda26e390842b3b82c0944094435880797332ad0bd0869d835e1f4094555c5f49c0944c09e62bff7a316780944094672d00944094409440944d942375b97fc0944e4c777500944173c0945651100440945e21ce22f28e7c54196dfa0dde404829938ddc6e515d264ec21dfb41ea136d0f02230094677bc09440944094436bac5be252857e787c6a2a1530a517554dd215f9165c2c29396f25a0318f59121abb4fb91d1642a98bdc070c6f8757a861f4368c2e09522a44a94553300b7f063740944329602410213b02c3075835924a06360d69777f902cd7634767cd91687980947505fd8f150c384aff7a890cc03a00945c62978c9e7cc9742f5068373610b6154f93d012a43d57876b71ab2a4900d811957a7132725dba793f9100945917c09440944094589000945c79c09450476308ce7e009452293f02809440947b48a988af15009440946a76454800944b8fb4260e8602614b1f809440944094409440944094616d4882425fc094409440945e83a86fcb217451e51b5576d25eda356877e7383891ad4b1838b7310e07e93bf35640944192c094501980944e03c094750a4416f3581b7e95842346d485c09440946669809440944094550d80945830c0944b7540947692a5738231d5427670d09040944185046a754180946c1d9e40006ede01a905971e19532a3a4e639f65cf7eca763e7f4289dd221107a738ee3e3e87ac75c943614c34855384c637e756c8168e247363217dc0944c347b1c994a418e0e34204045f212000c0940891c831010003002d18000096871e006a7060890402082122e647840428e99001c40300003801234402042c1011e2059402f470102542200c1408104140800410011000088b1a1010e18000053004382040401206000271e004861c0c0000220101162870402040030208a0008000800008019002000b2e0000106043800400c0402040040204e88080000002041000814002020c711060058706200012014000 else (if i<2 then 0x4bf518013775e233ddc788cff602233dde778cf7759e33ddd578cf7749e33ddd178cfb799a33f5e558cfe751633f9e448cfe745233fd8048cfe7012339fd788ce7f1e233bf8088cf774de33ddc378ce7f5e1239fc7848e7f5e1139fc7844fed45113bfa8840f7e1e103bf87840fee12103bf84840f7e9dd03df96740ff60dd03df83740f7e49d03efa6640fde95503fb94540ff64d503fba4440ff64d103fb91440ff68cd03fd91340e7f5e1039fc7840eef12103ddc3740ff640c03dee7788b7b59e22ded5788b7b4de22dec3788bbb99a22f6e5588beb51622fae4488bfa01222fac0488bf38ce22fe90388aef12102df6778477d59e11df5578477d4de11df437847bd99a11f7655847ed51611fb644847fc01211fb404847f58ce11ff103846ef12101fb5144077e1e200bf848802fe4e200dfa778037e59e00df9578037e4de00df8378037e49e00df917803be99a00f7a55803ee51600fba44803ee45200fda33803fa88a00ff2118027f1e200bd938012cf56004bb5180127e1e103503b000d64fc0eec060c5500944094741c6865409440947c60409440945d200c53dd8200945f54926675330700556a358646453d3c9a239174570f81644034005deb92562c9969376b02502b117d2e9d71384e60086a122980691896145011015f9e1b3504205a9d514125401bfb36ef625727750ebc44793869871c104094742f7f06687880945e27b5413f6c409462416904ca85a60a1f93707b07039e3a8d0ba65c9c0c9327363d298c7f4cce391d8ebe5b0f5e763380946f7080945171582aed5a034d0f828e8f6280b91946892e47d20d2e430094463215563650bb88713e8940ac0d6778128d451ce43780945193122dec23c094598b0239c0944094505af64f6d83dc4d7872736d0971c51e9680d42c725b80944094738e2a34fe149930409440945258c09447264165a52ef045972688088a5575334340e627f9209360195e1e4ba412c570375740944094409440945a32c094654983479017809440944094496eab42c094558ec0945c34a100b2186e6bf1688094772e633b00945c5d4094775e8094592f0981d87b7c0940944094777d4b6ac145e53c4e78c0947a58603f6668f5683a92391e40945e0f5c466d81097d2053aa7ac09450671113b105096f2f48796e3f24d5351564028b485ccc687a43cf0ac054eb5f593ecc7bab7d9520e272b22da26c0e023174b78a4c5180944149141b9e15a80a851ec866c51ac811ef722806c36b7660a789bd86c094409440946d33c64bd31a0262133bae774c5680944094409440947281954ffd048701eb42007725526e030094409451015b2f80946f0c6728758964289209892827845b8a184b5048e61934784057009447939a57fa4ca2778094574db9802a13d38d009440945859d38c293f8094611 else 0x453ef91114fbd34453ef0d114bfd68012ff56004bfd38012ff4a004bfd180137f9dc04dfd670137f4dc04dfd27013ef51804fbc34013ef49004bfd788cf7f1e233bfc788ceff5a233bfd588ceff52233bfc488ceff4a233bfd188ceff42233ff8088cf7f9de33dfd578cf7f4de33dfd178cfef51633fbd148ceffa2123bfd7848eff1e123bfd6848eff56123bfd4848eff12123dfe7748f7f59d23dfd5748f7f4dd23fed2648fef51523fed2448effa2113bfd7844eff1e113bfd6844eff56113bfd4844eff12113dfe7744f7f59d13dfd5744f7f4dd13ff51644fef51513ff51544ffd45113ffa8840ffe1e103ff96840ffe56103ff84840ffe4a103ff91840ffe9dd03ff96740ffe55d03ff93740ffe0dd03ff92740ffe45d03ff94640ffe4d903ff92640ffe45903ff94540ffe4d503ff92540ffe45503ffa4440ffe4d103ff83440ffe49103ff91440ffe8cd03ff92340ffe44d03bfe8840f7f1e103bfc7840eff5a103bfd5840eff52103fbc4840eff12103dfe7740f7f59d03dfd5740f7f4dd03dfc3740f7f49d03dfd1740ffe41903fbd4540ff74d503ff90540ff74d103fbd1440ffe01103fdd1340eff5a003bfd5800eff52003bfd2800eff46003dfe7700f7f4dc03ff90300effa2102bfd6840aff56102bfc4840aff4e102bfc3840b7f9dd02dfd6740b7f55d02dfd3740bfb49902fbd4540bfb49502fed2440bfe40d02bfe88406ff5a101bfd58406ff12101bfd38406ff0e101dfe774077f59d01dfd574077f4dd01dfc37407ef51501ff515407fd45101ff903406ff12200bfc388037f9de00dfd678037f4de00dfc378037f49e00ff9038027f5a2779fd589df6f522779fd389de7f0e2779fd289de7f46277df9089de7f422779fe8859e7f0e1679fe8855e7f0e1579fe884de7fa20379fd680de7f560379fc480de7f4a0379fd180df7e42037ddd370de7fa21279fc3849e7fa21179fc3845f3f9de66cfd3799b3f0de66cfd2799b3f45e66bf80851a7f5e1369fc784da7f5e1269fc7849a7f5e1169fc7845aef12106d7e779575f4de55d7c379575f49e55d7d17956efa2145fb8085176f9dd45dbc375176f49d45bf8085167f5e1359fc784d7cf515359fd784967f1e1259fd784567f1e115bbc48417cf51505dbc78912ef56244bbd18913ee42244dbe779136f59e44dbd579136f4de44dbc379136f49e44dbd17913af99a44f3e55912fe422449fc784d2fe02134ddc374d2bf5a034b7d580d2fb4a034bf5180d2fe02124bbe88452ef56114fb8084536f9dd14dbd674536f0dd14ebe66453cf95514bf808452fea2004ef968013de56004fd938012fe4e004fe928013fc46004dfa77013be99804f7a55013ee91004bbd58012ef46004dbe770136f59c04dbc370136f49c04ebe66013cf95404afd68012df56004bdd38012fb4a0)) else (if i<4 then 0x1642c6588b095f2bc578af15828e51ca394026c4bc929252484748e91c22e44c8890f21e43c8790f21e43c8790f21e43c8790f21e43c8790f21e43c8790f20e3fc7c0f01d0394720e31c43806f8dd1b83706e0da1b43606c0d819a30c5e8bc1762d8558a613624c4908a104208408800fa1f43e87b0f41e43b0740e61cc3806f0da1942904a0941282484708c1142204408810821042084108208410800f81e83c0760ec1d8390720e41c8390700dc190310600bc1702c0560a81482704c098130240480881102204404c090110200037f5a277dfd589df7f52277dfd389df7f0e277dfd289df7f46277dfd089deff5a277bfd589dfef52277bfd389deff0e277bfd289deff46277ff9089deffa2167bfc3859f7f9dd67dfc3855effa2157bfc3855f7f9dd57dfe884df7f5a137dfd584df7f4a137dfd184deffa2137dfe774df7f59d37dfd574df7f42037bfe880deff5a037bfd580deff12037bfd280deff46037ff9080df7f9dc37dfd570df7f4dc37bfe8849eff0e127dfe7749f7f59d27dfd5749f7f4dd27dfc3845effa2117bfc3845f7f9dd17dfd6745f7f55d17dfd3745f7f0dd17bfe8851aff0e146dfe7751b7f4dd46dfd2751b7f45d46bfe884daff5e136bfc784daff12136dfe774db7f4dd36dfd274db7f45d36efd464daffa2126bfd7849aff1e126bfc4849aff0e126dfe7749b7f4dd26efd3649affa2116bfd7845aff1e116bfc4845aff0e116dfe7745b7f4dd16bfe8841aff12106bfc3841b7f9dd06dfd3741b7f49d06dfd1741bbf51906efd2641bbf45906fbc38517ef9dd45fbd37517ef0dd45fbd27517ef45d45bfe88516ff0e145dfe775177f4dd45dfc375177f49d45dfd17516ffa2135bfd784d6ff1e135bfc484d77f9dd35dfd374d77f49d35dfd174d7df51535bfe88496ff5e125bfc78496ff12125bfc384977f9dd25dfd37497df4d525bfe88456ff5e115bfc78456ff12115bfc384577f9dd15dfd374577f0dd15f7d35456ffa2105bfc48416ff0e105dfe774177f4dd05dfc374177f49d05dfd17417df51505f7d154177f1e244bfd68912ff56244bfd38912ff0e244bfd28912ff46244bfd089137f9de44dfd679137f55e44dfd379137f49e44dfd17913ef51644bfe884d2ff5a134bfd584d37f9dd34dfd674d37f55d34dfd374d37f49d34dfd174d3ef51934fbd454d2ffa2034efd680d2ff5a034f7d580d2ff56034fed280d2ff4a034ff5180d2ff46034ff9080d37f9dc34dfd570d37f4dc34dfd170d3ef51434bfe88492ff5a124bfd58492ff0e124dfe774937f59d24dfd574937f4dd24fbd45493ef4d124fbc38453ef9dd14fbd67453ef55d14fbd37453ef0dd14fbd36453ef41914fbd35453ef41514bfe88452ff5a114bfd58452ff0e114dfe774537f59d14dfd574537f4dd14dfc37453ef51914fbd45 else (if i<5 then 0xc684020c10d840810209081000502fe5c68ef513a3209f3920d838157120c380f671d7d0ca8b752ddc44efa1951705cc5889cebe16da337889cebe865600356cd81f7639b830f458331d198511c0c50314f679d88545c180ea43b4f1ca8b811d39d2a2e0c0734139d862e0c06d09ba73b1cac136243060c10d84082420436104847a89d197241b07a545f3d44e8cbf7241b0756ae23e87060040889c99601e2bd44e8cbf2e403ab6089b1960428bd44e8cbf60403ab1c1c61728de8ae800c1c45485fc3303c1c45485f43303df83890d9c35e0c1bc667d99f06e178d06357bd44e8cb920d83bd44e8c8104e48360f115217e19f43303ddb74e76395161821b081020436102043610204086c20456ac3b728b833f5610d8408102090810d841211fbd44e8cc77ce48360e060c056fd5ab0cd554497490bf8f19f43a26188f158a85228138984a2411084401f0e870361a0c85c2a140984822900803c1c8d06833170b4582f150a4502a128904e221088c3d1e0e872381f0d064301b0b05429140b8482213074381a0c8603c14090402c0c05024100f03014060200800070054b716dedb5b6b6d6dadadb4b696cad75adb576aad45a4b47682cf59ab3565ecad93b25646c858fb1d632c5d88b0d612c1d81afd5fabe579af35debbd77aeb5ceb7d6bad1596b2d62ac157aadd59aaf55eaa552a9d532a4d47a8b512a2544a855029ed3ba774e69bd37a6f4d299530a5f4b69652ca594aa94526a4748a9051da3545a89d11a1f43a86508a0d41280cff9f93ea7bcf59e33ba764ea9d33a674ce69c737a6d4d89ad3566acd59a734667cce99732e654ca98f31661cc097b2ea5ccb796b2ce58cae9592ae54ca894d28e514a093d26e4dc9b9332624c49692b24a47c8d91522242c839072023f47b8f11ce39c708e11b2364698d319632c648c718e314608bd1722d4588a914627c4d89311a2244087b0ee1cc3786d0ce1842e8570a613c2584507e0ec1b82f04e07c0c81301e024007feff1fc3f87ecfd9fa3f37e2fc1f73ee7dafadf4be77cef95f1be07bef79eebdd7b8f61ea3d27a2f45e83ce798f31e53c778af0de13c1782efddf3be778ee5db3b6766eb9d53a774ce8dd039e738e71cd399730e59cab93722e45c8b9071ce39c638b714e25c438670ae15c1b82702dfdbf37c6f6de5bbb776eedd5b93726e4dc5b7b6d6d8db1b5b696d0d8db035c6b4d65ab3556a2d3da634c694d1da3b4768cd0da033e67aced9cb36664cbd9632a64ec999231f638c698cb1862ac4d88b0e618c2984306608c0d80b01600c017eafc5f2bdd7b2eb5beb7969ac9580ad95aaa953aa4142a7a4e09912ca4e4828e117a2544a86906a023ee7d8fa9f43e47c4f89ea3be760e71c837c6f8de9bc3766e4dc1b736e6d8d91ad35a698cd99331a60cbe9722e25b0b596a2d259cb3 else 0x507cb0d44f4cab74ec1be7ef88390eadb37068a9cf46a513d5880cc89669019751cfa81a59f477ca119f3e6a3be568d41a3eec8961035bac7c428112e416391c5c89f1c5c88e2e44707851840e0ed87083e3840e10895cf4a8d5a27ab14a252884a94539e9a7b394a273384b69d35c9a10451be7335ccd2331b1a7c8db4c6d3113da6ad2a344f502944814a212814a240ad0114021d9c56ee5a03481da0343501a40655cb38695997480cbe75065a03225019a4e91d274a501952e4cd212a5b5232a4ca994e443e22e653994464b66eadf0834da4b692f9d3610a1d99752159c3465d2032e9f2032250195621dbfa66a42376fd5bea0221116f4cdc8a02611b772df2b8ef55ba568d5be7b1cdba8ee63896d1d1a48868dc14668888568dea434e8dbb22e49086c25bac74d8dbb20adcab72ac99156416392e40d97205c811365c991864db8a56de30e107c7081c207371c2941f14a053b14ec3ab8cd95b6562842b0ed8707363838e0efa0368c21424143841b14de30a1100537148dea434e8dbb8e45c9210d84b736f44b9490601234215bd56e95be56e55b656f8d087cf9d363748d4113444408ae4439728dcab7315cc536e6297208cdd16c45b116c8c8b656468b62ed8dd10e5db510e5c7072e8cdb72e69b970e5df2b3f1143f1b0cb3f567e23e1b0d444890e24b514a1ab7f1df1687195be865a8be7ef4d3a46ed5bf7cf4dba8ee44b646a121f886ddc1346e09f346d5896f01f8813006a34868dbb22484096ef8839a0e4d0872215b9104c8907238b903638b901c5c80e4638d971c6958e230cb931c1db426c69b2b6c45b8a101db0e0e6c7071c1db3e36dcd37562053e9e6d6c756b5f095aad1b332adf3920d83a27a699a256f9c906c1cc9f7419ea27465f3920d83bf56f513a331dc907cd839144655be5e1c8391088cab7cbc8071ad833d44e8cab7ef9c906c1c30352d0cd388f5c906c1e7a944663b920d83be56d0c5106d112090e9c906c1e0b44480cc77ce48360eac1bd44e8cb920d83c706f513a32fdc906c1df2b32fd13920d83ab50f59a27e65c906c1d5b3747dea27465c906c1df2b971962232fc80756e4b2f4465f8720adb2f1b115218efa1981f4a8837a89d19a10cbb9601dea27466397201df2b55498037a89d1984d98101d01ea274663be60407075610204121023d6865c906c1e7197e894b920d83ab6865cbe0ed18439ad0cbf7c5c8300eada196cf981098d0cbf7cc080e0eac2040824204060e5b44148cb4a4bd03a6889c906c1e93444fccb920d83ab4064f294cee93282d11397cc03ca6889fbe2e4180756d11367cc08344525fbe60403ab40395ab3299db20)))))
def pred319_8 := batchRange 319 raw319 cuts319 8 3 layer319_7 layer319_8 12
theorem cases319_8_0 : pred319_8 0=true := by decide +kernel
theorem cases319_8_12 : pred319_8 12=true := by decide +kernel
theorem cases319_8_24 : pred319_8 24=true := by decide +kernel
theorem cases319_8_36 : pred319_8 36=true := by decide +kernel
theorem cases319_8_48 : pred319_8 48=true := by decide +kernel
theorem cases319_8_60 : pred319_8 60=true := by decide +kernel
theorem cases319_8_72 : pred319_8 72=true := by decide +kernel
theorem cases319_8_84 : pred319_8 84=true := by decide +kernel
theorem cases319_8_96 : pred319_8 96=true := by decide +kernel
theorem cases319_8_108 : pred319_8 108=true := by decide +kernel
theorem cases319_8_120 : pred319_8 120=true := by decide +kernel
theorem cases319_8_132 : pred319_8 132=true := by decide +kernel
theorem cases319_8_144 : pred319_8 144=true := by decide +kernel
theorem cases319_8_156 : pred319_8 156=true := by decide +kernel
theorem cases319_8_168 : pred319_8 168=true := by decide +kernel
theorem cases319_8_180 : pred319_8 180=true := by decide +kernel
theorem cases319_8_192 : pred319_8 192=true := by decide +kernel
theorem cases319_8_204 : pred319_8 204=true := by decide +kernel
theorem cases319_8_216 : pred319_8 216=true := by decide +kernel
theorem cases319_8_228 : pred319_8 228=true := by decide +kernel
theorem cases319_8_240 : pred319_8 240=true := by decide +kernel
theorem cases319_8_252 : pred319_8 252=true := by decide +kernel
theorem cases319_8_264 : pred319_8 264=true := by decide +kernel
theorem cases319_8_276 : pred319_8 276=true := by decide +kernel
theorem cases319_8_288 : pred319_8 288=true := by decide +kernel
theorem cases319_8_300 : pred319_8 300=true := by decide +kernel
theorem cases319_8_312 : pred319_8 312=true := by decide +kernel
theorem cases319_8_324 : pred319_8 324=true := by decide +kernel
theorem cases319_8_336 : pred319_8 336=true := by decide +kernel
theorem cases319_8_348 : pred319_8 348=true := by decide +kernel
theorem cases319_8_360 : pred319_8 360=true := by decide +kernel
theorem cases319_8_372 : pred319_8 372=true := by decide +kernel
theorem cases319_8_384 : pred319_8 384=true := by decide +kernel
theorem cases319_8_396 : pred319_8 396=true := by decide +kernel
theorem cases319_8_408 : pred319_8 408=true := by decide +kernel
theorem cases319_8_420 : pred319_8 420=true := by decide +kernel
theorem cases319_8_432 : pred319_8 432=true := by decide +kernel
theorem cases319_8_444 : pred319_8 444=true := by decide +kernel
theorem cases319_8_456 : pred319_8 456=true := by decide +kernel
theorem cases319_8_468 : pred319_8 468=true := by decide +kernel
theorem cases319_8_480 : pred319_8 480=true := by decide +kernel
theorem cases319_8_492 : pred319_8 492=true := by decide +kernel
theorem cases319_8_504 : pred319_8 504=true := by decide +kernel
theorem cases319_8_516 : pred319_8 516=true := by decide +kernel
theorem cases319_8_528 : pred319_8 528=true := by decide +kernel
theorem cases319_8_540 : pred319_8 540=true := by decide +kernel
theorem cases319_8_552 : pred319_8 552=true := by decide +kernel
theorem cases319_8_564 : pred319_8 564=true := by decide +kernel
theorem cases319_8_576 : pred319_8 576=true := by decide +kernel
theorem cases319_8_588 : pred319_8 588=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_8 : settled 319 raw319 8 3 layer319_8 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 solved319_7 (width:=12) (groupsN:=50) (by decide +kernel) ⟨cases319_8_0,cases319_8_12,cases319_8_24,cases319_8_36,cases319_8_48,cases319_8_60,cases319_8_72,cases319_8_84,cases319_8_96,cases319_8_108,cases319_8_120,cases319_8_132,cases319_8_144,cases319_8_156,cases319_8_168,cases319_8_180,cases319_8_192,cases319_8_204,cases319_8_216,cases319_8_228,cases319_8_240,cases319_8_252,cases319_8_264,cases319_8_276,cases319_8_288,cases319_8_300,cases319_8_312,cases319_8_324,cases319_8_336,cases319_8_348,cases319_8_360,cases319_8_372,cases319_8_384,cases319_8_396,cases319_8_408,cases319_8_420,cases319_8_432,cases319_8_444,cases319_8_456,cases319_8_468,cases319_8_480,cases319_8_492,cases319_8_504,cases319_8_516,cases319_8_528,cases319_8_540,cases319_8_552,cases319_8_564,cases319_8_576,cases319_8_588,True.intro⟩
def layer319_9 : Layer := (50,10,6,2,17,69,5,6,(fun i => 0x246ac406aa058c79a406a2484c58cca4406caa69631e91a406aa058c91a406b4caa129632468a1aa84a51032e91a42a82e58629a406b2889d312220cc169a406b2889d312232ed8686b2889d294388832b8cdd6690b2889d31212ec8a79a40689d312228ca4406b26612232a9e696348f289101ac9997922327bb5241ac999294388c9ebb74a4e10b266121327ae2a4406998488c9e91a406b267504891246901ac99d4122246901ad326743292224686b2674a50e22e324690b2671212a82e58718a91a42c1a675048924691a406b4c99d0ca488ece91a1ac99d294388bb691a510b2675c484b8a91a40699c488aa058c91ab101cc99d0ca48924691a28699d28e214ba469099c4842ae91a40699c489246b00898b0e134aa00b058c60f004a24ca00ccc163223bc132a9e682c16348898384d2a802c1632260e12cd4cade80345d0b129632263a134aa00ca510b8c898d8ed2a802b962871800a2a1c488c800987a6488cbeb18caa79ac16348002b26712238b04d2a82e58a1c712c00299c488d2a816c0c00239499c22e00210a99c4ae002b267122151493129210900e8d8d0c8a8a09890888078706864585c50504c40443a383c30342a282c20241a181c10140a080e0203001843d0ac1500bf2f73c6ed39ce0b62d1b30c4af8b72c0aba98a126c9523687a067b1d26e99e62176581464b1123f0d82f8a4250841b860128481183a0b81e03801ff9dffeb3ffd57ffa6fff0dffe93ffd17ffa8dff4dbfe937fd16ffa0dff517fe9affd25ffa2bff417ff227fd34ff869ff493fe8a7fc04ffc67ff48ffe89ffd03ff807ff40bfe80ffe00bfcef7f59efeabdfd37bf86f7f49efe8befe66efcabef517df227bd14ff009ef013ef19ff903fdc45fd847fd002814030954329b0ace0d9236e42f104d123da07b98521d5799dda475d528d0fb5a081085f626de064c45940065792dbe065abbc480641cbaadad264d64606466070c0645af7389884a2064065896064064064c26065b54f2b1b406406406406406459e06488a065f1b202c0a490601802200c22))
def pred319_9 := batchRange 319 raw319 cuts319 9 2 layer319_8 layer319_9 12
theorem cases319_9_0 : pred319_9 0=true := by decide +kernel
theorem cases319_9_12 : pred319_9 12=true := by decide +kernel
theorem cases319_9_24 : pred319_9 24=true := by decide +kernel
theorem cases319_9_36 : pred319_9 36=true := by decide +kernel
theorem cases319_9_48 : pred319_9 48=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_9 : settled 319 raw319 9 2 layer319_9 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 solved319_8 (width:=12) (groupsN:=5) (by decide +kernel) ⟨cases319_9_0,cases319_9_12,cases319_9_24,cases319_9_36,cases319_9_48,True.intro⟩
def layer319_10 : Layer := (1,4,6,0,1,2,0,1,(fun i => 0x1c50c12c818a10200000a0ff502a01))
def pred319_10 := batchRange 319 raw319 cuts319 10 1 layer319_9 layer319_10 12
theorem cases319_10_0 : pred319_10 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved319_10 : settled 319 raw319 10 1 layer319_10 :=
  advanceBatch pairs319 (raw_faithful 319 _ _) cert319 solved319_9 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases319_10_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra319 : Lower (roots 319 true) (graphGoal 319) 11 := by
  apply finishAug (cap:=10) 0x8000000201020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=319) (l:=11); decide +kernel)
  have eq : (nodeValues raw319 1 (nodeBits layer319_10 1 raw319.length 0)).toFinset = (roots 319 true).toFinset := by decide +kernel
  exact eq ▸ solved319_10 0 (by decide +kernel)
def past319 : List (Nat × Nat) := (319,11)::past317
theorem pastOK319 : AugKnown past319 := augExtend extra319 pastOK317
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra349 : Lower (roots 349 true) (graphGoal 349) 7 := by
  exact lower_map (ms:=([64,49,98,118,135] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra215
def past349 : List (Nat × Nat) := (349,7)::past319
theorem pastOK349 : AugKnown past349 := augExtend extra349 pastOK319
def sampleCols351 : Array (Bits × Bits) := #[(0xb65bdd596879a5aecaa0dd709dc728a37ce6536147bcb3d0337c37d0a3ee7279be10a81084a756213b6b5d35e936aa0aac757de073916714e95a2af35327ccb19ec6c44ce5bd81b98561dcc4c1aad90d1a20c14c22340b31acd33ce0de24ca60,0x4344e49002814e28f095a4041d32204ba640c601b9c8d6004781b12c0c22412b80e6a5b9994462012230900c014a8082440654032102604804a0ab3100548218f824740c5b52ba42d659c8e603ac84a0c204380203402318c9308e04624c860),(0x53ad357d61972a3ace7547ac5f73fd42c76771328c7cf1b9c7bf8ef11a3238d950d14898019b1f3ec58d1d3e76832ab8538995ba8e0e61e47641c8572ad833a470229470313f9656253862c1467149b9e674a41ce744f7404918b356b3a30451,0x220010002281000060c284992c0089430511910484224283090284a012210b09059110200221100c018004283203028012018090800400202000c0400a401100304190903802901a00106041040000a142558024dfc045400008b30691810011),(0x4d5a0be2e01d4e3dfd7f30cfd386fa81974289a2ced75d0976561995fb573cf73c8846801148e4e4cce662a467a58559829ef32b7972eaf398e45aacd613371527240e69b38c39412494aa265ad31d68cd9875556c131492f904882e6c6e5e47,0x9020204983048081d207844d34646b0a04e4a534a19195876b57b55edd6b4f0f26acdc6f5dc00408800208405a40118809e532a5930e84098241804d00002170324446bc3482161e78593265bdb5f58bca8555320021092f9040828686e5e44),(0xfbd6f9db9782d3d5bb48bec33808e5bf9e7d8cce4697cee82a137e2fab438faf992c16455240a9a6aff23fcb904c99d4dcd2034354ed920d821e4569ad5bc8e916923b3a2bc739b41892cda332860ec2019bd8a1d89fc02a9289428b5689b89a,0x40c4891300020550a24c862824a1a0431e318520a5a6c6a1094880000000400108042219080021200642134300088840484000000000000102100121041a88881c821b0024971c9418304c9120008000000008805f9580280001428316818082),(0x56d5cc9bf1da95e3f3ea9e1cf5c9c6f238bb461103100948262735fff2bdfba97f24a000c62742db3294e4503d15530d11bccae4ab5d8cb97a99b739adacfe5bbcf695acce4a00c982438104d38d13847a948de5d0286d56666157a8284056bd,0x980000a04500a801502220969a045da0410a701b4001100c720724e53b359ae847f195a4666a0093209444103801520111b082a0894980985881300821002442207c80bd1a48804b828a23409f813780f29e847580086d46626015082840161d),(0x0,0x0),(0x44713e9d8fa5d274d44a7654a3b743c0376bbc71b93d4ce6dee9ba717da29c48e343012a2810fbdb646fd9d852fb57636d6e661ed9007c0a05a7b58654ecc942650bd18186045fd7462c98996e88ab503cec4652a169aacd1126499007d4df44,0x40d1c01c0808122786186300028520081a20042003948d68267d3b5d69de9454ca462319ddd8ca82646cd850405015634d2c2402400048000004040444a8c0028592490504a50e8410288cbc72cbbb583ca84c522029aa0d110448900610de44),(0x0,0x0),(0xa82012269e732980450278905b44cfaeb97f5c5f7d8fd6a75948d11566d79e18d7021167280010409a1082c788f8fce77f61acd5a6ff9ffefde7f8c6d240031b2149e4bbd34ae1e3ff945e992800a0020893c666a0c210ad06feb9296875a115,0xa122102096116008592218d4d94a4fa0a1ce58d348493000d00204a092212aa835b9dce6222410408800008400a000040000084526cf17be65c3e0c282400315226d84fad348a163e7c61200882000a3425793258042108006fab12868642111)]
def pos351 (j : Nat) := (sampleCols351[j]?.getD (0,0)).1
def neg351 (j : Nat) := (sampleCols351[j]?.getD (0,0)).2
def raw351 := rawDecor 351 pos351 neg351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs351 : properPairs (graphGoal 351) (asRow pos351) (asRow neg351) :=
  chart_pairs (m:=351) (p:=pos351) (q:=neg351) (by decide +kernel) (by decide +kernel)
def pk351 : List Packet := [(0xb0057c0000,0x0),(0x8005780001,0x0),(0x80056c0004,0x0),(0x380056c0004,0x0),(0x800d380010,0x2),(0x88007c0040,0x8000000000000000000),(0x388007c0040,0x8000000000000000000),(0x80017c0100,0x0),(0x380017c0100,0x0),(0x7005740002,0x0),(0x37005740002,0x0),(0x7005380011,0x0),(0x370007c0140,0x0),(0x6095300200,0x0),(0x604d182000,0x0),(0x6810748000,0x0),(0x62405e0000,0x0),(0x60254c0008,0x80000),(0x5085300202,0x0),(0x5800748002,0x0),(0x5005640006,0x0),(0x500d182008,0x0),(0x52005e0008,0x0),(0x50054c000c,0x0),(0x5024640042,0x200000),(0x5014640044,0x200),(0x52006c0104,0x80000000000000),(0x52005c0108,0x80000000000000),(0x4005300013,0x0),(0x4005280015,0x0),(0x4005180019,0x0),(0x40005e0048,0x0),(0x4001380111,0x0)]
def cuts351 := pk351.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert351 : certifiedCuts 351 cuts351 :=
  certifyPackets pastOK349 _ (by decide +kernel)
def layer351_6 : Layer := (1,0,6,0,1,2,0,1,(fun i => 0xfe00a51444d035000fe))
def pred351_6 := batchRange 351 raw351 cuts351 6 5 emptyLayer layer351_6 12
theorem cases351_6_0 : pred351_6 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved351_6 : settled 351 raw351 6 5 layer351_6 :=
  advanceBatch pairs351 (raw_faithful 351 _ _) cert351 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases351_6_0,True.intro⟩
def layer351_7 : Layer := (26,5,6,4,9,32,4,5,(fun i => 0x5d0ee5d15dcb43ad2d2d1ad2502c0a826090220801c06c16858178460601200076b5ad6739ce694a4e7394a107bd69394408fe8c870b3c7f4a68855e3fa321c2af1fd190e1279beacd108b4bf5a6884d67da53442279ed780a113aee1cace89c7f2255744ff48508a227f953545113fca8a24689ff20a51340ffa22c89a07fd11340d128beac870b3c6f526884de2fab21c24f1f909a21178ee1caf09347e2256740e3f112aba071f88949d039dc44a2881fe44511340d402ce1bd0801a1daf254581a034f01a981a034b0ffb4d18ee8a3ec706518cd6d55c55c9b054101aa5da4afa139294200922))
def pred351_7 := batchRange 351 raw351 cuts351 7 4 layer351_6 layer351_7 12
theorem cases351_7_0 : pred351_7 0=true := by decide +kernel
theorem cases351_7_12 : pred351_7 12=true := by decide +kernel
theorem cases351_7_24 : pred351_7 24=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved351_7 : settled 351 raw351 7 4 layer351_7 :=
  advanceBatch pairs351 (raw_faithful 351 _ _) cert351 solved351_6 (width:=12) (groupsN:=3) (by decide +kernel) ⟨cases351_7_0,cases351_7_12,cases351_7_24,True.intro⟩
def layer351_8 : Layer := (155,9,6,3,52,193,7,8,(fun i => (if i<1 then 0xf2733619cca6331184c05f2f178bc5c2a950a04c2490476361a8c054261208836190a850261208844220f078341208038180a0502814060301002ffa2136dfd374db7f49d36dfd174daffa2126dfd3749b7f45d26efd3649affa2116dfd3745b7f49d16dfd1745bbf49916bfe884d77f4dd35dfd274d77f45d35bfe884977f4dd25dfd17497df4d525bfe884577f4dd15dfd274577f45d15f7d25457ef4d914fbd26453ef45914fbd35453ef49514fbd15452ffa2123dfd7848eff5a123bfd5848f7f59d23dfd5748f7f4dd23dfd1748ffb49923fbd1448effa2113dfd7844eff5a113bfd5844ffb0a113dfd6744f7f55d13dfd3744f7f49d13dfd1744ffd45913fdd3544fef45113fdd2344eff5a013bfd5804eff4a013ff93640ffe49903ff91640ffe4d503ff92540ffe45503ff92340ffe44d03bfe8844b7f5e112bfd6844aff56112bfd3844b7f59d12dfd5744b7f4dd12dfd1744bfb49512fbd1444bfd44d12ff90344a7fa21679fc3859e7fa21579fc3855e7fa21379fe8849e7f0e1279fe8845e7f0e117cfd3799b3f49e66cfd1799a7f5e1369fd7849a7f5e116cfd6745b5f4de55d7d279575f45e559fd784d75f55d359fd784967f5e115bbe884536f59d14dbd574536f49d14ebe66453cf95514ddd788cf7759e33ddd578cf7749e33ddd178cfb799a33f5e558cfe7452339fd788cf774de339fd7848e7f5e113fb51444e7f5e013bbd4804efe42013bfa8840f7e59d03df95740f7e49d03efa6640fde95503fb91440ff68cd03fd91340f7b59e22ded5788b7b4de22ded1788bbb99a22f6e5588beb45222fce3388bfa40e229fd7844b7d59e11df5578477d4de11df527847bd99a11f7655847f58ce11ff103847f988a11df517847ed45211501188622476500bf980643343e962c224cd5ce19624075f026ee1df50c604f04c92c9a3f62615f3d05b9d393a89c7510026c34570cc981265bc371a5754e105809bce2809bb93ed2e50f409b026c09bc16409bec63d258d77a7f4dd409b026c09b026c09bac3409b217a72b8646028883c09b11b009b026f052ad2ee8c026c09b026d564026d70b14ec09b466a27da54157e8c8e661026c09b187e542a81c036026c09b8cb705c61a3801026c09b349ca155181d4d4d19a30a06b1838d6116d999ec53026fe48026ff82026e517a1afe864dc3354e91009bea4e322d1cea323947576e82809b2e1409b026f3081103b207446b7785a7579f66123f026fc5aa1ba11ed19b52188f27005e1c863026f81c951fa84d40d68e19a809bbdc951b2e5d2494d5686ff1307316025f14e8ab1397009178604bb4ab9ed106fce0d414d6c8297648462e4d0b9416663566a3657a3038f354238c820040a2a05540024e180110c5c0bc00480001a28603080c00200046800a00280281c00710006033c0010a else 0x89b5938b28b289b8b18b118789b8b54d28b49d84964d21e74a26d23d68b49b65a2ccf5a26e2c068b01d59a26e2be2bd23c76c5905445a5b545aa46851626e26e26d48ae8ae2868ae5046e26c889b40789b5077a2dcab6ca6260aaaca5c60a8b41eca5c6ca52d42a11b2a91e26e789b9a26e93a2b0e6d13a954eb2239b38e6c93ac89b89b4226e26e2ae2ae2aca19010735b01684fb22dc6a587564e13ccb86628743b6c2c08534ac886a587614db48f32e198a1d0ec0274e63e26f51a961d0274e63ec88aa587674e63cc2866287435f6b009d398fb3319b89da274e63ccb866d87430410613c689884fa189e48a13e88866d89dfb690410614c68986dc9997eab214e8626922853a2218062092ca5b62092ab296d892ca5b0050050810410440533db1989220533e26133e218cb1c4cf6dc88669860331c92930389868082265ba60899b1ba6265ba4038038395b323b2900e0d97690410411013414cf8a804104134104404401f0f074381b0d06430170b054281309044200f4703a1a0d86230198b85a2c160a4482711084411c0f06431140b0442013070341a08840280a0403c0a0301800e3bbdbecf5fabd3e8f3b9bcbe3f0b7fbcdd6df65aed66a74fa4d16833d9ccde672f94c8637198ac56230b83c0dfefb7cbd5e2ef73b7dbad162afd6aaf55a9d3e9d4ba451689419ecea71369acc65f2f964aa51269248a411f8f4763710813e1d6df6a31976af572b558a75026d2a9449a491a863f9e8)))
def pred351_8 := batchRange 351 raw351 cuts351 8 3 layer351_7 layer351_8 12
theorem cases351_8_0 : pred351_8 0=true := by decide +kernel
theorem cases351_8_12 : pred351_8 12=true := by decide +kernel
theorem cases351_8_24 : pred351_8 24=true := by decide +kernel
theorem cases351_8_36 : pred351_8 36=true := by decide +kernel
theorem cases351_8_48 : pred351_8 48=true := by decide +kernel
theorem cases351_8_60 : pred351_8 60=true := by decide +kernel
theorem cases351_8_72 : pred351_8 72=true := by decide +kernel
theorem cases351_8_84 : pred351_8 84=true := by decide +kernel
theorem cases351_8_96 : pred351_8 96=true := by decide +kernel
theorem cases351_8_108 : pred351_8 108=true := by decide +kernel
theorem cases351_8_120 : pred351_8 120=true := by decide +kernel
theorem cases351_8_132 : pred351_8 132=true := by decide +kernel
theorem cases351_8_144 : pred351_8 144=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved351_8 : settled 351 raw351 8 3 layer351_8 :=
  advanceBatch pairs351 (raw_faithful 351 _ _) cert351 solved351_7 (width:=12) (groupsN:=13) (by decide +kernel) ⟨cases351_8_0,cases351_8_12,cases351_8_24,cases351_8_36,cases351_8_48,cases351_8_60,cases351_8_72,cases351_8_84,cases351_8_96,cases351_8_108,cases351_8_120,cases351_8_132,cases351_8_144,True.intro⟩
def layer351_9 : Layer := (24,9,6,2,8,37,5,5,(fun i => 0x1e5cc2455824d034661979730985609340d10f64761e5ce3098450903465536197574d124558248b1993987574498560922c439960775744984509238b1956587d744c24558248d19885744c2560923471185d13091c509234655844c2450923581955a05d130984248d1c45585d13098450923581955a02c46d545364f2818488170d011b55950c3812a12205c340b11b55a50f2818488170d02db55a50f04a8451e05c340b6c46943ca0612165c300141334664a0d80012ce48664a0d870255a50f8485970c00523462836096da50f5ca8488000441d234a0d800155234628360544844403c383630322c2c282620221d1c1e181a15141610120c0e09080a040701018008a591f88405e6e56bb297eb353a6d1a7e37980a2431c8bc481c0902401ff4dbfe937fd16ffa6bff497fe8affe33ffa47ff44ffe09ffd12ffc237f59efeabdfd37bfa4f7f45f7f3377e55f7a29f78cffc81fee22fec22a022545a063430180306bd76787589f0af8b17f82062f70187240624a0180300600c58386cc83e59c9030063450536d0f400c5d5ba40300061))
def pred351_9 := batchRange 351 raw351 cuts351 9 2 layer351_8 layer351_9 12
theorem cases351_9_0 : pred351_9 0=true := by decide +kernel
theorem cases351_9_12 : pred351_9 12=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved351_9 : settled 351 raw351 9 2 layer351_9 :=
  advanceBatch pairs351 (raw_faithful 351 _ _) cert351 solved351_8 (width:=12) (groupsN:=2) (by decide +kernel) ⟨cases351_9_0,cases351_9_12,True.intro⟩
def layer351_10 : Layer := (1,4,6,0,1,2,0,1,(fun i => 0x1c508c2061032c100000a0ff5000de))
def pred351_10 := batchRange 351 raw351 cuts351 10 1 layer351_9 layer351_10 12
theorem cases351_10_0 : pred351_10 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved351_10 : settled 351 raw351 10 1 layer351_10 :=
  advanceBatch pairs351 (raw_faithful 351 _ _) cert351 solved351_9 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases351_10_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra351 : Lower (roots 351 true) (graphGoal 351) 11 := by
  apply finishAug (cap:=10) 0x8000080001020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=351) (l:=11); decide +kernel)
  have eq : (nodeValues raw351 1 (nodeBits layer351_10 1 raw351.length 0)).toFinset = (roots 351 true).toFinset := by decide +kernel
  exact eq ▸ solved351_10 0 (by decide +kernel)
def past351 : List (Nat × Nat) := (351,11)::past349
theorem pastOK351 : AugKnown past351 := augExtend extra351 pastOK349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra371 : Lower (roots 371 true) (graphGoal 371) 8 := by
  exact dropLower (q:=355) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=355) (l:=7); decide +kernel) (by decide +kernel) (by decide +kernel)
def past371 : List (Nat × Nat) := (371,8)::past351
theorem pastOK371 : AugKnown past371 := augExtend extra371 pastOK351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra375 : Lower (roots 375 true) (graphGoal 375) 9 := by
  exact dropLower (q:=359) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=359) (l:=8); decide +kernel) (by decide +kernel) (by decide +kernel)
def past375 : List (Nat × Nat) := (375,9)::past371
theorem pastOK375 : AugKnown past375 := augExtend extra375 pastOK371
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra379 : Lower (roots 379 true) (graphGoal 379) 11 := by
  exact lower_map (ms:=([81,98,118,135] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra191
def past379 : List (Nat × Nat) := (379,11)::past375
theorem pastOK379 : AugKnown past379 := augExtend extra379 pastOK375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra377 : Lower (roots 377 true) (graphGoal 377) 8 := by
  exact dropLower (q:=313) (extra:=true) (s:=64) (hints:=0x4000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra313 (by decide +kernel) (by decide +kernel)
def past377 : List (Nat × Nat) := (377,8)::past379
theorem pastOK377 : AugKnown past377 := augExtend extra377 pastOK379
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra381 : Lower (roots 381 true) (graphGoal 381) 9 := by
  exact dropLower (q:=377) (extra:=true) (s:=4) (hints:=0x200000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra377 (by decide +kernel) (by decide +kernel)
def past381 : List (Nat × Nat) := (381,9)::past377
theorem pastOK381 : AugKnown past381 := augExtend extra381 pastOK377
def sampleCols383 : Array (Bits × Bits) := #[(0xd2b139091958c3a1685accc9d1663620bab60ab432c3c9e1e1a8293a796419b8d475180585e835440d35c2748a66a315efdd04f3aa05326f900e6c31081e84c385751202862b5d4cc442812b090ec823c24d0188d45a9862e5c0c6a1e424c4f0,0x40a0300118084301405004810020022092160084220009418000011811040828c071000404a020400c3700308f20a211ad508972c00842c5840c68201a070001a475104210294b04840183a8090c8800800d01805048186041c042218424c470),(0x7235361a83634148f2244de6c8c998ac0c3d4ac8478b51472d1658127d4845642d290c852128b7a52c82c15087810c909dd1384f588ae48da43916300d2c51f3085653b6d9686cff4aa48031160875df0d206266124121282b4993d639a0609,0x3014160001620108d004058200c098000404000000804102040240022c0041200809008000202320080440f00c910680025008935c1b80a5242904700f0cf3a188045104c8484cb60ae08411060021960d20604000002128224811c631a0009),(0x698026cc38c0247e3577a3925b90d67c75bd1d7dd2bcd03b16ec1749888fa8ad2f0d7454cb96de24d99e3a412e342ccbc4e0bce4a9488a104484a14aca4660042069bad22bb71aa02c01e531a3143858280128bbedb5c499504d560f8c846793,0x480002883840042e3066a1825b90947d61b9197d9196902116ac10c1c81db085270d42548a00cc04590e3a409a3466033480b4668a180354040c41888a062044256dba4a237312109f41a538e3002840080128bbedb5c489504854038c846790),(0x449590a46666ce32d0a0c3a31078c4e74d2cf3d24b0427c38c431030b082625b193aac3a71ec61eba8558533655d5cabd679c8ba44e2d01802b53ea6c60180309249abc15064292c201eb4d0b4b7b6910188ac910ac80324092b4ba84a69684e,0x49510040420821040004220004800800004008040002082804300202002024a1030200271402121a071843325411894c3784a9041e2f428c1d32c2664818030d01004810004690c000810800c369411018884000040012409230aa842680842),(0x7946cb8a0a851da664c13967db012adde6b0e309b9aac6067d2546b6466aebc8589aeae7947778afbdf1c9571bd7363a1081541d2ea00903122c12c80c5a06d88ea82b00e2d310c079621dc132a943a8563160783e32252cbb68150621162bad,0x3942890200851ca004813146d402284d64a0a30899a2c6045520d6864468a0850c824a408215508811885bc4109e046a1085340d3e0409121a2093c9015877ca088aeb0063d290c179720c51328143a8563060782e322408b20815062112238d),(0xbc1e6a5b5413094bc3a9b23e9f76319512cf38d0c4873cf48fceb40d295395c6b5a04736280dc41ab14892211241998c660960c8a4c59cae7393145201f4de2ad9a87e04227ad9151f4104380a92488637661a56a4c5cd011c2129cce35aa3d0,0xa4124a5844110842822d90169d16101500c91810888610200c84d003081291c435004622080c840ab148a60110411d8c4209748824e59c2a7193160a44c0dcb2598866a16a46248952c80c148692408633621856a484c5011c2109cc634a2280),(0x34985d6c5b9dacf325d2524ad9b8d2c62613837ed81aacc8194cacad739762323c561ebb661a68093da82bc93803492444a7f34dc108f2c9cc5642834872108d49362e900430a0698e88e345d4915a69a92d14109b4a8cd5b110ab2976476c0,0x8484c1a0d8ce221d34248d028440422830395d01b0e40184c08ac1107001030421e1ba618400b55b8330b3020d90ce587f50c0020424a8952c28bc070004c45b22eb224b0b04904094144f0915a69200d14109b4888d59110aa0906466c0),(0x0,0x0),(0xbcfafc37d7affad98f1d7c5da20d4b128d50c743227c4309763e8b459eada0b0a36d5348a8018e15198254acd89c62431086e0361a9a43d027917d6e3175be2858b20c041031b0112f17866d574020400d2cd744120b76dbd24a7443147b1119,0x100820030202000101000809020143028c00c6422268430862180b0016a100300048100800000a04488458cc08bce243108480261a1803d106204140013822090020191014b090522d372369304020400c040200120b32528248740304111119)]
def pos383 (j : Nat) := (sampleCols383[j]?.getD (0,0)).1
def neg383 (j : Nat) := (sampleCols383[j]?.getD (0,0)).2
def raw383 := rawDecor 383 pos383 neg383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs383 : properPairs (graphGoal 383) (asRow pos383) (asRow neg383) :=
  chart_pairs (m:=383) (p:=pos383) (q:=neg383) (by decide +kernel) (by decide +kernel)
def pk383 : List Packet := [(0xd005fc0000,0x0),(0xb005ec0004,0x0),(0x3b005ec0004,0x0),(0xb005bc0010,0x0),(0xb0057c0020,0x0),(0x3b0057c0020,0x0),(0xb004fc0040,0x0),(0x3b004fc0040,0x0),(0x9005f80001,0x0),(0x9005f40002,0x0),(0x39005f40002,0x0),(0x9005dc0008,0x0),(0x39005dc0008,0x0),(0x9001fc0100,0x0),(0x39001fc0100,0x0),(0x8005cc000c,0x0),(0x38005cc000c,0x0),(0x8005b80011,0x0),(0x80059c0018,0x0),(0x80017c0120,0x0),(0x380017c0120,0x0),(0x8000fc0140,0x0),(0x38000fc0140,0x0),(0x7195300200,0x0),(0x722ce00400,0x0),(0x1722ce00400,0x10),(0x7055c40800,0x0),(0x78a18c1000,0x0),(0x178a18c1000,0x1000000000),(0x704d982000,0x0),(0x7809784000,0x0),(0x17809784000,0x10),(0x7810f48000,0x0),(0x73405e0000,0x0),(0x7005b40012,0x0),(0x7005740022,0x0),(0x37005740022,0x0),(0x6224e00401,0x0),(0x6185300202,0x0),(0x6800f48002,0x0),(0x620ce00404,0x0),(0x6015c40808,0x0),(0x600d982008,0x0),(0x63005e0008,0x0),(0x6115300210,0x0),(0x602ce00440,0x0),(0x6034c40048,0x80200),(0x60a18c1100,0x0),(0x160a18c1100,0x1000000000),(0x6010f48100,0x0),(0x6001dc0108,0x0),(0x5005c4000a,0x0),(0x5000f40102,0x0),(0x5005982009,0x0),(0x5005c4080a,0x0),(0x5801384011,0x0),(0x5105300212,0x0),(0x5005b00013,0x0),(0x5005980019,0x0),(0x5000f48102,0x0),(0x4001384111,0x0)]
def cuts383 := pk383.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert383 : certifiedCuts 383 cuts383 :=
  certifyPackets pastOK381 _ (by decide +kernel)
def layer383_8 : Layer := (78,7,6,5,26,97,6,7,(fun i => 0x715ba5c946e5bfaaf79f35bfb6c2313c38d8478d84463dbf88004431b3d749b20000189b4c0b50d920c6318c1d83a06c0b81582a84c0984fe11423c2d0590b315a1ec3f46f0ae1742703d0740cc1f82e83f03a06c0b80f01400823468b162c58b162c4850603f7efddb970d19af5cb1424468d1a24489122447cf1e3c78f1d3870d9b366cd9b3668d1a3264c99324c9932448891203c58a0a101830608101014bf5ae99a2117977a97552708bd2fd6ba653845f1df551129ba2966f5ec3845d148dfad7552f289c7ed2baa97944e9f695d33442272df56eaa5e113b5bad61d2f089d3ed2ba657844eddabd9128a2273be5aeaa45d038dfad64d4ef08c7ed2b26a3384693ead8f4b48714af52c7a5a438a5da563d2d21c52f51b1e9690e297c858f4b487143f5ec1a5a438a4fab60d2d21c52bd4b069690e297695834b48714be42c1a5a438937a97552713bc8febb5a8389de1bead935444ef25f56eaa5e27786fab7553129bc3bd4baa9894de9da45a948c86f0bf5aeaa6251786fab7553128bc2fc9b5a83845f15eb52921c02f3e6aed3a02514df22369d0128a67993a5e409452dcc9d812bc2292afaed6a0e114c57ad54c8708a5d993b02677452c5eb58713ba290ef6ac890dd14c57ad44486e8a633d5a224374531d6951121ba298ed468890dd14c772144486e8a4b5d5baa9788cf4ce454ee8a4670ef52c9aa2233973a975527119c3bd4baa98944e1f695d54c4a277e442c3a45113bf22760522889cf395b2691440f3d84d2328a2077e452c1944d03bf25768a22681df909b4511340f7c95522889a07ee42291444d03ef25328a22681fb92884511340fdc8bc22889a07f649dd1444d038e7ab64d22881cb755baa9788465daa5d549c4232bdaed6a0e211b1ead61c4ef08dab56b0e1148467d855a2881a032de56eaa5e2009772975527100280228e5b823360a63d021830146804e065161113c04ea9d369792404e0275e41a5923cb8d813809cbad0274ac0b5604e0273a2a61a823b19813809c04e1d0013a73e04e957013809dd9c027291409ce3eec1aec9973c9dd47013af0284c5caa690f0f016e626a4e55e6899cc86fc885d945e37e03a53f18de0be1bf11247f078e6b044b4db50f6e23930266a408d7855ea7158ad2d46d9bb8c1662d92229705c0000c31006021470062647ea04d0800a7780))
def pred383_8 := batchRange 383 raw383 cuts383 8 5 emptyLayer layer383_8 12
theorem cases383_8_0 : pred383_8 0=true := by decide +kernel
theorem cases383_8_12 : pred383_8 12=true := by decide +kernel
theorem cases383_8_24 : pred383_8 24=true := by decide +kernel
theorem cases383_8_36 : pred383_8 36=true := by decide +kernel
theorem cases383_8_48 : pred383_8 48=true := by decide +kernel
theorem cases383_8_60 : pred383_8 60=true := by decide +kernel
theorem cases383_8_72 : pred383_8 72=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved383_8 : settled 383 raw383 8 5 layer383_8 :=
  advanceBatch pairs383 (raw_faithful 383 _ _) cert383 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=7) (by decide +kernel) ⟨cases383_8_0,cases383_8_12,cases383_8_24,cases383_8_36,cases383_8_48,cases383_8_60,cases383_8_72,True.intro⟩
def layer383_9 : Layer := (486,12,6,4,162,607,7,9,(fun i => (if i<3 then (if i<1 then 0xba03cc07980f301e64bca0798b7001e6070276460664db603cc067b20290d2a9647c2de6116f4bc4bdbc856ba0be60726325fe919aa3ae731d4a350ca4ca3146835333a836e6f61f40f30077b6e92823e5b316e03cc079b043d978c52a39363b3b31503cc10e80f37372c5242b9c0f301e6a31e07980f301e603cc8ecc59f700016d48443fbf2389a685be4aa1081e60e62fd7c0f301e61a81ea02141441b498f79b00f301e603cc7adc0f325c59eee079b0c161baa63c079a01b390cd510c2847528521cd9dff08b1dc0c0d93207982e0ead830a3e18251901e603cdfb6af9381e69f799edfe8e82ca7d71b3db23f3a6859d62d35fefc15047afada787e9a81dc345ace0012d9583aaccaa930ed0ae65056734984d16f3bb730d008ea3cb45756282f1336d1e87db8e9578511b92e62a99dd945ab29f0c8116adb320da1ed9b3c259b9e06b807adc701e603cc4c6cc7d88dd948b083da29865b9e12be757821529e25e66b40f334e4cc4d6906416872b7f94079b000ea1c6f1a49b80f301e696d6fe60868dc6469b8079bf79e1d0481861646b801e658a589bc0f31065400f58240f301e6ff97f77253101e603ccf0f40f316b0c37c0798923884480cfdd1c42487a450d661c920ca559ae6c2a82b9f81e65868fe500f301e6bdca079b22101e6ab0a079a945aea303cd4e7c0f35dcde267ec640f35240f01671700f301e603cca7467b29da7d307e8401e49eb4a1190c714d29250c6927bd4da29d2c03cd7a58a5e049d03cd6e640f31084ce3fa539fbd3e482f6a705b2b0fa7b3ab9064c0f301e6d98855bfdab634af8ec5163a5fdc30b357fabb3031a5f6a107ded981cfa14d4485d4891b25489cc473c0f34f34f4ba07980f343551c27a3f87ac4d138d36f2e40f32986aa91913a20f81e6051bcc880f301e6885f3434d42ee04f65a07980f302796d8a3a4f71b847f03cd55457a238a8190d73a7dd7c5c8de7873646e39cad28db19335e1b9412c25e3b3aef6f9742c78e300f34e4beaaefbe096ddd05275394900f35e28b3a8cde5019ea7ae0861a9cc11009e393407980f32138dc9e079bbcd01e6d78ce3a36ed2e712d14ea7c2d1259b61e190bb05e81e6438090810a5c7027f0ebdf450181e603cc08c40f301e603cce0a68b201e6589407981dc01e6caa807980f3414c218c07980f310ef32fe295687ba0c8a028079971667077c3bb3f08562d5b03cc337f247ea2392d09b58387183c10d0658d17360c40504900001600a06360048f08007b50834085008429e12540361e0000a0a14231280050122081003600c81022cc0e000c000020004c0224006003c0000a0000310000010e0410a060410902040820204005120018d0668005000c1850e1800006081020c4c300001008c0600187201410812180021804025003010928040840400000 else (if i<2 then 0x7cfcbc4ee81d7f3140ba077dca502e81dfb2740ba077dd5522881df71348a207fcc9d22881ef75328a207fd88ca2881f775108a207ddcbc22881fb74ee8a207ded4446681f7b2f119a07eed3bc6681ff322919a077ed5522681f7b11489a07bed4ca2681ffa03289a07ded4422681f7b2f089a07eed3ba2681ffa22e89a07fcc8a22681ff622889a073dea553281c7fb34bc2073de4d22881ff2a2889a075fabd11308d7ea7444c235fac50f308dfca543cc235fac507308ddead41cc237f88507308d7ed54bc4235fa4d2f108d7ea743c4235fb5527108d7e9349c4235fabd07108f3e9153bc23cfa44cef08f3ed113bc23cfa9c4ef08f3e8713bc23cfabc4ef08d7eb149bc235fac506f08ddead41bc237baad06f08df6a941bc237f29506f08dfe2141bc23dea4546708ffa01519c23dea44c6708f7ad1119c23deabc46708f7a8f119c23eeb3bc6708f7aa7119c237f95520708ffa07281c23df94420708f7e2f081c23ef93ba0708ffa46681c231fe4d51108c7f934bc4235fa8d0f108c7f9349c42357eb507108d7ea341c4235fb5523108f3ea313bc235fac522f08f76d108a423ddabc22908f768708a423edb3ba2908f7aa3119c23fca8a46708d7eb1489c23fd88a20708ffa22681c233dea553280c7fb34bc2031fecd27080df6d548a203bdb4ca2880ef6a728a203ddabc22880fb6cee8a203fca8a46680ff622881a035fd552f10067f134bc4015fd552710057f5548c401cfc9c4ef0073f2313bc01cfcbc4ef0057f3149bc015fcc506f005df2d41bc017bcad06f005f72941bc017f49506f005fe2341bc015fcc522f0057f3140bc017dca502f005f75548a401ddcbc229007b74ee8a401bec4d4670077b2f119c01dec8c467007bb4ef19c01fcc8a467004ff13519c01dec9c4670057f31489c01fd88a2270057f31409c017bcad027005f729409c01df8bc4230077e27108c01ef93bc23007fa46708c01df88c423007f622908c011bead532bc477a954ca7117f552d21c51fad41c4ef7cc9d0128a557ad41c2298de44cee8a5739148a467fc88a22681d5ead41c422a07796da0260622e715533a75e494ad843b205e23b2f84a6762c2bd89a6270bb60619f3c18dc4235d6a8deefeaf014468ee376f480aced45cf010ff60687a3e8c6ab8af4e01e669dcfceec7d20175d1354d47e23de47a7af3fd6d4005ea2f8f6980f357265fb2079892b01e67f5db0a8339c6f9bd4cdf62647640e03cc079b1eb01e6025db60232bba707a01926018958b17c7c0307a0501e6172007980f301e65fc2d6d00121acda6ec07980f301e603cc07980f3771a21a66c3c49c81e636d807989a901e611bc73ab455d5d3e471ad6a83a01e691525c5ec874e7ce56be451bd601e603cc07980f332edf3b712426d88fcc23c7f89c75d81e67716079ac4894 else 0xbd3fb141ccef6fc850733bd3fb140ccef6bead0333bdb7a940ccef4ff552713bd3f9349c4ef4fe8d0713bd3fd548c4ef4fe4d2313bd3fa740c4ef1fe4d5113bd3fd54bc4ef1fe4d2713bd3faf41c4ef57eb50713bc7f9348c4ef4febd0313bc7fb154ca6f1ff553129bc7f9354426f1fe4d2309bc7fb340c26f4febd0309be3fb133ba6f1ff553121bcfed548c86f9fac52321be7e9148c86fbdaa52321bcff5548486f97eb4d101be6fab34406f9dea4d101be7da534406f9fa8cd101be7f2134406f1fecd2301be5fad28c06f9beaca301be77a928c06f9f694a301be7ea328c06f9fc84a301bc7fb340c06f97eb48301be6fab20c06f9dea48301be7da520c06f9fa8c8301be7f2120c06f1fec55328bcdfad54ca2f1ff553128bc7f9354422f1fe4d2708bc7fb341c22f4febd0708bd5fad41c22f5fa8d0708be3fb133ba2f1ff553120bcf7d54a482f9dea4d100bc7fb349c02f9dea4a700bc7fb341c02f57eb50700be77a921c02f3bead53283cf7a954ca0f5debd1128a677912bca299de44a728a5e7ab41ca297dc850728a5f727404a29bdcbc8128a677d33442295df552f08a677934bc229dda0d2f08a677d32bc229ddc04af08a577af41c2299df4c8708a7379153ba29adf4ccee8a7379133ba29edc04cee8a737d113ba29cde1c4ee8a6779133ba29cdebc4ee8a6779129ba293decd06e8a577b141ba2975eb506e8a5e7ab41ba297d69506e8a5f6a341ba297dc8506e8a6779121ba293de4d20e8a57baf444c675ee8d11319d7bb143cc675eec503319df3a940cc675ef552f119d7b934bc467dec04af119d7ba343c4675ef5523119d7b9348c4675eebd03119f3b9153bc67cee44cef19fbb0133bc67cef444ef19f3ba313bc67cee0c4ef19f3baf13bc675eec522f19d7bb140bc677cea502f19df3d548a467dce4522919ff30148a467fca0ca2919ff30128a467dcf4422919f73af08a467ecf3ba2919c7f935444671fe4d2f119d7ba743c4675ef5527119c7f9348c4675ee9d03119f3ba713bc675eec526f19d779148a4671fec553289cfda554ca271ff5531289c7f935442271fecd2f089c7f934bc2271fecd0f089d7ea343c2278fec4cee89df6d548a227dda4522889ff28748a227fd80522889ef6d328a227dda44a2889f76d108a227ddabc22889fb6cee8a2279eec4c6689ff2a2919a271ff5531209cefd54ac8279bec52b209ee7a94ac8273fd5521209e6fab3440279dea4d1009e7f213440271fecd2f009e3faf2bc0279beacaf009e77a92bc0279fc84af009c7fb343c0279beac8f009e3fb133b827abeaccee09eb7a933b827afc84cee09ef72954ca077dca553281dfd2543ca077bcad03281df72940ca079fd4cd1081d7f554bc2079fc4d2f081f7b074bc2079fd4caf081f3f1153ba07afd4ccee81f3f5113ba0)) else (if i<5 then (if i<4 then 0xc24ac4aa48e48c48a4744684504404344163fe3fc3fa3f63f23f03dc3d03c23b23b03ae39639639439239239238e38036c36035c34c33a33832832631831431431030e30a3083083063063042f62f42e82d42ba29c28c27425e25a25625425225024e24a24824624424224023e23e23e23e23e23c23a23623423223022c22a22622622622622622422422422422422222221e21c21a1fe1e21e01c41ae1ac1aa1aa1a41a41a019a19819819619218e18c17a16a15a15815414613613012a11611411211010e10e10e10c1081061041020fe0fc0fa0f40f20ee0ee0ea0e80e80e60e60e60e40e20e20de0dc0da0d80d40d20d20d20d20d20d00b009008207406604c03c02c00e0015fe8d072bc57fa740caf15fe8d0f29c57faf40ca715fe9d0f28c57faf41ca315fe8d0713bd7fd548c4ef3fe8d5329bd7fa3444a6f9fe44a329bd7fb140ca6f7dea50329be7fd334426f5ff552309be7fd328c26f9ff4c8309befed548c86fbfa852321bcffd548c86f9fe8cd101bedfad54ca2f3fe9d5328bddfad54ca2f5fe9d1128be7f9129ca2f5fec50728bdefab41ca2f7dea50728bdff2141ca2f9ff4cd108bd7fd549c22f9ff4ca708bcffd549c82f9fe9cd100bdf7a743ca297debd0728a7779133ba29dde1c4ee8a5f7d549ba29dde4526e8a7779129ba29ddebc26e8a777af08ba29dde1c22e8a57fa343c4673fe4d4ef19cff9348bc673febd53289efda554ca277f69553289d7faf444a273ff552f289e7f914bca279fe44af289d7fb143ca277dea50f289e7fd33442279febcd1089d7fd54bc227dee1d2f089e7fd32bc2273fe4d4ee89f7e9148ba27dfa44a2e89f7ed108ba273fecd22e89fbea2e83a27fda3d22889ff68f28a227fdb3ba2889ff6a6e8a227fda83a2889f77af08a2273ff552f209e7faf3440279fec4cee09ef7a933b827bfc84cee09dff2343ca077fcbd03281dff5548ba07fdd3ba2881ff726e8a207fdc8ba2881ffb22e89a07fdc8a22681ffaa2e89a075fe9d0f108d7faf41c4233fe4d4ef08cff9349bc2377eb506f08defab41bc237dea506f08dfda541bc237fa8d06f08cff93519c2377eb506e80defab41ba037dea506e80dfda541ba037fa8d06e80ff6cee8a203fda9ba2880e6fab54caf19dea5532bc47fa754caf11fe8d532bc67f2154caf11fe85532bc56fab54caf15dea5532bc57f2154caf157eb5072bc67ba721caf19fa8c832bc4efab54caf13fc85532bc47fd549c8f11ff552323c47faf54ca719dea55329c47fa354ca715dea55329c63faf23ca719fa8c8329c47fd54bc87197f552d21c65faf4b487197e3d2d21c65fa34b487197e0d2d21c47fd548c8711febd5328c677a954ca311fe9d5328c67f2154ca315dea55328c63faf23ca319ee9c8728c47fd54bc8311ff552720c53fa7444cef4fe8d1133 else 0xc2b0a093db7039d15950e8a043da13615380d0a9d2b0a499383c7a4c08c499d1b95138a09b70f038b03838383838b038283828283828c108f028282829e02828b029083a8828d0d21c72e9d15950e8e42a78a0425b6bfa11d15950e8e0ac2a78a04259d82bfc72e9d15950e8e0aa10a04259dca3415128e0da78a08a0a70282968f02a102a10b02a32285028b0282800300951db70a0c3d9d15950ebda78a043dae9d15950e8a0401819f8a8d38299d3e8a21298c95361d3e8a018c9f8b9e82478bc1248c0b3f1d0a1502bd8282908f028282829d828282968f02829d82a2029f909e9d85028282829d82909e8f94459147341d1b838e4b8a09c9bdb90b4cc4ce1d1b9513c28c2e0a09c9bdb70183950e2a0a380283950e288a36c1b60d9d150a479c4a4bd4551513a88d8a09a7363702039d150a229eb682839d150a221e47d236408c4449b74f9d1b95138a098283950e288a368761d0721c06e1b06a1a06619063182601805e1705a16056150521404e1304851846110421003e0f13a0ec388e0380d8350ca324c8320c42e8b92e0ba2c4b02a8a12809a240962348c22c8a22488228812007e1d4741cc721c4761b46b1a4689a06e1946418861180661745c16c5a164589605e1505314851140561344c1284912248138451104310841100470f43b0fe370da358d4338cc328c8318c4308c0370b42b0be2709a258942388c2208621080270781d0701b068190601f05e0f03a0d8340b82c0a828090220803e0701a0580e0180200010015724b24323b23723322f22b22522121d21921521120d2092052011fd1f71f11eb1e31df1db1d51cf1cb1c51bf1bb1b71b31ad1a91a51a119b19518f18918718717f17b17717116b16716315f15b15114914514113d1311251211191111091030ff0fb0f70f50ed0eb0e70e10dd0d90d30c90c50bf0bb0b70b30ad0a90a70a109d09709308d08b08707f07b07707106b06305d05705304d04703f03903102f02d019016ff4fd6fd4fb8fa0f90f84f72f72f72f5ef52f34f16ef4edcebcea4ea4ea4e86e6ae4ee32e16dfcddedbedbcd9cd9ad8ed8ed8ed70d52d50d4ed4cd48d46d44d40d3ed3cd3ad38d36d34d16d14cf8cf6cdccc0cbeca6c8cc72c54c3ac2ac26c08c06bf0bd6bc6bc4ba8b8cb6eb50b32b14afeae8ad2abcaa6a90a7aa5ca48a34a1ca089f29dc9c49ac99297895a9409309109008fa8dc8da8bc8a689087285c84082c81a8047f07da7c67b27b27b27b07ae79679679479478678278078077e77e77e77a76075c7447347227106fe6ec6d46be6a66a66a46a269e69c69869669469269068e68c68a68a68a68a68a68a68a68868268067c67c67a67a6786766766726726546386366346186166166125f85e05c65ac59258456654c53c5385365225225225205145124fe4fc4f84f64d84d64) else (if i<6 then 0xca7bfb22e9d199511aca78a07bdb22e9d199511aca78a079d15950ed28e0a8a0427aca221369dbd321511aca38a078d0e3bb21d19aca38a078d0e3a321d199511aca38a078b0c35b21d199511aca38d0e321d199511aca20a078d0e321d1995118e0d2ca38a07b69d15950ebda78a042ea14046cd4731134c0a093fa4154001c71d15950e8e42a78a043fbdbd9d15950e8e42a78a042ea136d49d15950e8e0ab6278a042ea1399dbf9d158e8e0aa8a784369d8a1527a1368e0a1d1528c6cdca504c128e0da788a08a36955528a7a8a1150e1d0a3697900201b32e9d15950e8e42a78a0426a13d81a002322e9d199511b6aa8a07a5a10b3db22e9d15950e8a0425a144b22e9d1995118a07a5a150a7a89d158e8e0a8a0421369d9525c695128e0da88a08b6a0a7448bb22a9d1995118a07a5a10b0c46311d1b0a0939498e3d80030095400c370a3da321288a319d15448dcbb61d1a15122d8a081db74044c0339d1a15120a081db7145447b94b9d288a2c520d8abe47b715499d0a2c1e81819d1b9513c4cb8a09a58dc981c79d4b950a28b6018c83820b82361d1a151233ad8a0822a11e9da28236371a120822a11e9d8a1d151d95319d288a2c4044a1319d288a152c3e3ccbb91531a88a2c523b4bb9319d288a2c52354bb915319d28ac520d8aa4be403915319d288a2c0d8abe4bb715319d288a2c371d1a15120a0822a12d9e9d83838f03839e038283838282838290968f02829e02828383a202a8472e9d15950ebd8e2c8a043fa136c2a79d15950e8e0a8a043fa12c9d8282c2c72e9d15950e8e0a8a04212c9d828f02b62e341d1a95128a08a2211e1db6ae9d158e8a0427a115403dc24ace1d1b1342ab3fa415404301c72e9d15950e8e428a043fbdbdc72e9d15950e8e0a0427a136bd9d15950e8a04362e9d158e8e0a8a0427a13d9d9552bfafae95950e8e0a8a04369d9d2ea7a10e151d0a36858201cba9018c8d401b9d0a3681a90b0d1d0a3681a15295290cbe9d0a4bc98185820201c72e9d15950e8e2d278a0426a13981c5b01d18ad278a06a6a14837a6c91d14c64baa0a2d01c80238b09d198e2ca78a07a5a10d02023d9d15950eaca78a0425a1211d0a1525acc5c84bc99d19a78a07a125aca1258b9d15278a2ca12c9d0a1525d09d15950e8e0aaca78a0425a1369dc5b09d19aca78a07a5a10d0e02021e820b82038b2b0137498c3d8a15434b31950e524ec8d253498a0e251dc50b0c498a15250b818e019d1b93aca78a09bd95498183a9023da7b18a150e25499dc50b0c0bb18a15251d8e318a1525018cb6520b0d138a1549b647d238150d40c50a018b52408d1d3e8a1501a90a453e954bc9818ca7820d820b818181a7b64c150e498a01ab8e4c1d0a150c49c09d1b95138a09a50b3f0bcb8c441d1b9513ad0a09800300c01d1b15130 else 0x2552954bac1552c9a554b1d4ac50b1d0aec725aebdbdb622509a0836d09e50b63dc2bdbdc2d0a14bb78c0e0c403db60ab63db8a251bfbdb6163fd1a8d49d1a0836d49d4bd31d1e1d0b1d363dbfbd9abdbfbdb6363db647d3b647cbb633c7a8d50bc4b64bc047a8a2a11a550b9a27c2a5bdb63db63db6513f84bfd140432fd2a78a3db61d0a1a0836d2a78a4bc99e39c4d28a4eb63db63d98063fbdc288c99508cbbdbf91bdb6331d2d0a2d3db61604c9a4cf2ccbcf36cf36c38d1149a152a908c9bdb6363dafaec71eb68bb68e524e8e498db60ccf0cc3990cc09940880ba549a13fa13fb20dbdb63db624390da4390db99e243724390da2b90dbdb60e0dd20e0dd21dc00c0b8e0dd21dc00e0db63603b91d1b8e4b8a09c9bd83ac36279d15950e8a8a043fa11d8e09c2bda536211d15950e8aa78a041dbf8e3d839e1d9d15950e8aa78a043da10e038e910f839d1bcb8a09c9c4bd80038144954b8a3d8003813d95449c13838a09ca154bac1103b41d1b8a09b944bd8000bd83954481a79d15950e8e0aae8a043fa1381d81a11d15950e8e0ac2a78a042eb81db19d15950e8ab6278a043fa1399d8e42bd83ce1d1b9513b70a09c9bdba252e9d15950e8ab6210a04399d8e3fbd800103ce1d1b95138a09bdc9819d15950e8e0aaa278a043fa1381dcc3295110e0c17278a0726381f4a110e0c2a278a0746a6381f151cca15110e0c171c8726329f0a4db85546b295110e0c2a27871f0a38504a4c110e0c170a07381f4d951ca601c72e9d15950e8e0aa10a0427b81db19d15950e8ac2a78a0436211d8e3fbd83ac42ae9d15950e8a8a0436211d8e3fbd838003813dcb8a019d15950e8e0ac2a78a042321381d81c72e9d15950e8e0a8a042321381d8383838b0383839e03828382828382af321d15bd950e8e42a78a043fa13682c71d15950e8e0aa78a043fa1321d82cc15128e0da8a78a08a73420d5471d15950e8e0ac2a78a0421321d82b69d158eaea78a04211544bd81c71d15950e8e428a043fa13dbd9d15950e8e2ea78a043fa136d09d15950e8e0aaea78a0436213d9dc295950e8e0a842221369d8a1d21220e128a369d15100201b32e9d15950e8e2d278a043fa13981bfb32e9d189510ad278a06b32e9d189510b7ad278a068c0e379540331d2a0a2d01bc02322e95118e2ca78a07b8a38d3a82322e9d198e2ca78a07b8a38d2002322e9d199511aca78a07b6a38b35b482322e9d1995118e2ca7b8a38d38cb82322e9d1995118e2ca78a078d0d02322e9d1995118e2ca78a07b6a3bdb22e9d15950eaca78a043d3c4bb22e9511aca78a07bbbacbb22e9d19aca78a07c4b22e9d199511aca78a07b5b4cbb22e9d199511a)))))
def pred383_9 := batchRange 383 raw383 cuts383 9 4 layer383_8 layer383_9 12
theorem cases383_9_0 : pred383_9 0=true := by decide +kernel
theorem cases383_9_12 : pred383_9 12=true := by decide +kernel
theorem cases383_9_24 : pred383_9 24=true := by decide +kernel
theorem cases383_9_36 : pred383_9 36=true := by decide +kernel
theorem cases383_9_48 : pred383_9 48=true := by decide +kernel
theorem cases383_9_60 : pred383_9 60=true := by decide +kernel
theorem cases383_9_72 : pred383_9 72=true := by decide +kernel
theorem cases383_9_84 : pred383_9 84=true := by decide +kernel
theorem cases383_9_96 : pred383_9 96=true := by decide +kernel
theorem cases383_9_108 : pred383_9 108=true := by decide +kernel
theorem cases383_9_120 : pred383_9 120=true := by decide +kernel
theorem cases383_9_132 : pred383_9 132=true := by decide +kernel
theorem cases383_9_144 : pred383_9 144=true := by decide +kernel
theorem cases383_9_156 : pred383_9 156=true := by decide +kernel
theorem cases383_9_168 : pred383_9 168=true := by decide +kernel
theorem cases383_9_180 : pred383_9 180=true := by decide +kernel
theorem cases383_9_192 : pred383_9 192=true := by decide +kernel
theorem cases383_9_204 : pred383_9 204=true := by decide +kernel
theorem cases383_9_216 : pred383_9 216=true := by decide +kernel
theorem cases383_9_228 : pred383_9 228=true := by decide +kernel
theorem cases383_9_240 : pred383_9 240=true := by decide +kernel
theorem cases383_9_252 : pred383_9 252=true := by decide +kernel
theorem cases383_9_264 : pred383_9 264=true := by decide +kernel
theorem cases383_9_276 : pred383_9 276=true := by decide +kernel
theorem cases383_9_288 : pred383_9 288=true := by decide +kernel
theorem cases383_9_300 : pred383_9 300=true := by decide +kernel
theorem cases383_9_312 : pred383_9 312=true := by decide +kernel
theorem cases383_9_324 : pred383_9 324=true := by decide +kernel
theorem cases383_9_336 : pred383_9 336=true := by decide +kernel
theorem cases383_9_348 : pred383_9 348=true := by decide +kernel
theorem cases383_9_360 : pred383_9 360=true := by decide +kernel
theorem cases383_9_372 : pred383_9 372=true := by decide +kernel
theorem cases383_9_384 : pred383_9 384=true := by decide +kernel
theorem cases383_9_396 : pred383_9 396=true := by decide +kernel
theorem cases383_9_408 : pred383_9 408=true := by decide +kernel
theorem cases383_9_420 : pred383_9 420=true := by decide +kernel
theorem cases383_9_432 : pred383_9 432=true := by decide +kernel
theorem cases383_9_444 : pred383_9 444=true := by decide +kernel
theorem cases383_9_456 : pred383_9 456=true := by decide +kernel
theorem cases383_9_468 : pred383_9 468=true := by decide +kernel
theorem cases383_9_480 : pred383_9 480=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved383_9 : settled 383 raw383 9 4 layer383_9 :=
  advanceBatch pairs383 (raw_faithful 383 _ _) cert383 solved383_8 (width:=12) (groupsN:=41) (by decide +kernel) ⟨cases383_9_0,cases383_9_12,cases383_9_24,cases383_9_36,cases383_9_48,cases383_9_60,cases383_9_72,cases383_9_84,cases383_9_96,cases383_9_108,cases383_9_120,cases383_9_132,cases383_9_144,cases383_9_156,cases383_9_168,cases383_9_180,cases383_9_192,cases383_9_204,cases383_9_216,cases383_9_228,cases383_9_240,cases383_9_252,cases383_9_264,cases383_9_276,cases383_9_288,cases383_9_300,cases383_9_312,cases383_9_324,cases383_9_336,cases383_9_348,cases383_9_360,cases383_9_372,cases383_9_384,cases383_9_396,cases383_9_408,cases383_9_420,cases383_9_432,cases383_9_444,cases383_9_456,cases383_9_468,cases383_9_480,True.intro⟩
def layer383_10 : Layer := (310,12,6,3,104,391,6,9,(fun i => (if i<3 then (if i<1 then 0x8486f3fd8945e7fb120bdef52417bdf4ca29bbc89453f70128a6efa2114ddebc229bbc38453b7cee8a6f722633fec04c67bde888cf7baf119ef71e233dee8c467bdc188cfbbcef19fe745233dee9c4673fd8944ff6a2889cff62413bbeac8277bd4904eff21209dfea6503dfd44207bf97840fbf4ee81fee45103fed19a07fd91340f7e91308efda2211dfabc423bf4788477ea7108efd0e211efb3bc23fd633847fe20708efd46211fda8a423fb5144077f2f1006fe4e200dfc8c401dfa77803f7229007f68ce00ff908c012fd690e2779128a28159eda418c50942cc25128662ba026dd98409b0136026c04d8d07c62f9dbe04d809b0136de6413e009b0275743bb1518910136026c04d809b180b15f3a1cba095807b9f804db02b76038cc804d9d070e77449c04d809b1510026de43ef540136026c04d9268c657bd720a7968f6e2719682bc809b0031026c30aff98013634d204db5766662026ce3865970136813804d809b56b1b98fd466161ac155d22734b77100af026cbcc409b6f2c026d19bc84e8136617c510d4278136724fbc75419b210026ca471d38d00d419dc2e009b264d026d2a829680136b03c52d9d00208c8088883383b2060026c04d8e8066f4026d026809b3cfd29ba04db700d448025e24b409b0136026d9c8ed6c8136026d80b6d10b41b0d79e07ee4524bf41aae36c09b670605813808e1a9ed7624253a348c2a29acd71846d626edaccd9e2a809b07131438baddd17044c00582af7e0d0136fc7204d86595111026cfb9c09b5afaa90c316809b70a1964d2a03c3f1d0a4a3f4a9cc5152dcde4873bb174f6a4013eb24f58baf2975527306f1da503490f112ea24f8149d1e32cfb7ddc8e85053c69720d2ffe08a3c55d65aca3eca4c17c09b0c79124a588c09b013619df0a21b7aac40016bf3a841f54aeb06053350942e46b59378d809b66e0d02f10c9342945df15bb95409b30f080bd9c10c905a5bb5da1c3b19a0136f26604dad844a37026ce32809b623f522cd26409b7a9504272a101640136026c1c497729cf705ecd0aac4b14040e05c19ee6c22d6026d4b30a80b80958f0c0f6c102ce4ac8ff4d4952a474b47004dbf75c64271a8b147382e4243c51c2ae535013620cbc0652535c89a4b921c134ddb07e0b2d86009b6ed3844c04d89370a908503312809b62e3e52fcb0a12c7b141d61e0948494c34026c04d809b0136118c04da0032ac5c4fe702009b6e0ab844742516f6e534e578817678f87d58e774aa846ca3a68f82bf8b45c6e6f4f4998c43464ac4c7819b409b070d2217419809b2cf37637daec24c06cf1410c000408528010630101604338904908628904710030000108820d0a11c00520010141036c029724c68304b00000a1c12c50440002411000150440c01010080011403120c90821420800c5345 else (if i<2 then 0x21e2041ea1cc1b619a18416a15413e12c1120fa0da0c00a608c07205c042028016001ffd389dfffa313bfffa6537ffec4a6fffd194dfff8329bfff42537ffebc26fffd384dfffa309bfffa6517ffec4a2fffd3945fff8728bfff42517ffebc22fffd3845fffa308bfff4dd17ffe9ba0fffd1741fffcef19fff45e33ffe0bc67ffd078cfffd3289fff62513ffebca27ffc7944fffa1289fff5e113ffe9c227ffd1844fffcee89fff4dd13ffe8ba27ffd0744fffcee09fff9dd03ffe9ba07ffd1740fffa2681fff9de11ffe9bc23ffc37847ffc6708fff9dd01ffe9ba03ffc37407ffa2e80fff8cd01ffe89a03bfe995e37fa72bc6ff0e578dfe8caf1bfc195e2ffd32bc6ffa6538dfebca71bfc794e37fa329c6ff06538bff4ca71bfd784e37fd328c6ff5e518dfe3ca31bfd394637f8728c5ffa6518dfebc231bfd38463bf8733bf7f06677efe9c4efdfd189df7fd113bf7f5e277dfe9c4efbfc389df7fa313beff06277bff4ca6fbfd894deffb129beff22537dff4426fbfd784df7fa709beff46137dfe0c26fdfe774deffb121bdff46437bfe8486fbfe880df7fa301beff06037bff4ca2fbfd8945effb128beff22517dff4422fbfd7845f7fa708beff0e117dfe8c22fdfe7745effb120bdff4e417bfe8482fbfe8805f7fa700beff0e017bff4ca0fbfd3841f7fa3083f7f9dd07efe8ba0ffbe99453f7af28a7ef1e514fde9ca29fbc39453f7af08a7ef4e114fde8c229fbe77453f7a6e8a7ef0dd14fde8ba29fbd07453fb8f319ff706633feebc467fdd188cffbcef19ff745e33fee0bc67fdd078cf7fd1119eff5e233dfe3c467fdd388cf7fa3119eff06233eff3bc67fdd378cff7a2919dffa6513dfec4a277fd8944f7f91289dff5e513dff44227bfd7844f7f8f089eff4e113dfe8c227dfe7744ffea2e89fef45113fef19a277fd8904effaf209dff42413dff44027bfd7804f7f8f009f7f9dc13ffd4ca07ff97940fff0f281ffe46503ffc0ca07ff97840fff23081ffe9dd03ffc9ba07ff91740fff02e81ffe44d03bff4ca077fd7940f7faf081eff46103eff3ba07ff90740ff7a2881ff78cd03fee89a07ff479847fe87308ffd5e211ffa9c423ff677847fea6f08ffd0de11ffa83c23ff633847fea0708effa2211dfebc423bfc788477fa7108eff0e211ffa8c423dfe77847fea2f08ff78ce11ffa89c23ff903846ffd3280dff5e501bfe9ca03bfd784077fa7080f7f9dd01fde8a203fde33407ff20680ffd84501ffd3bc01ff937803ff06f007fe45e00ffc0bc01ffa33803ff227007fe04e00ffd08c013fe995e27fa723c4ff464789ff4ca713fd790e27fa321c4ffa65189febc8313fd390633f9133be7fa2277cfe9c4ef9fc389df3fa313be7f06277cfebc4ef3fd894de7fb121bdbf5a437bbeac86f7bd490defda521bdfd46437bfc else 0x538d0209f21302c7ac36482a702090981e2d61b241538d0209aa1303c5be58d4d920a04121303c5ac364828d02090981e2d3be00d40af3c54421303c5a302097be4e84c0b7ac1a9b24153810484c0f16ccc9007626cb427cc161e0990b13255be1835eccacbd09f305adb21625f33be6482c06964a13e60b0f04c168b12a533ea5769973cb0425c55509f1e0982d16254a680306c1453d625aa84f982c0982d16254a67d6c6497cb12a13e60b0f60b410b12a5300043113f5e84c0f160013d58390981e2d649aee109f30587d9642c4d5000873f5e84c0f1746f56196c6afaaf509f305990b12a800244b1eb01c84c0f16f673fab6509f305878b12a9a9b24b828d04a50981e2df004ad4d927cb828d0209098163d29b24b82810484c0f1694d925c1468104d50981e2df256a6c90502090981e2d29b24146810484c0f5c2df006a0541e2a210981e2c02e02a0f151084c0f16340827cb90981e2dea96a6c92e0a04121303c58c1b451810495ea942605de988860dbf2909f305ad8b12f521b24b82a7020923d426078b82f5a9b24153810484c0f1745eb5364970502090981e2c035029071e2a21fa1303c5d1440410c1af53a1302c02e029071e2a21fa1303c5804e0520e3c55f88426078b4060b02583c5897af41213e60b0b12947221e0ec74391c0dc6c35190c05e2b150984a2411888421d0e06c32188b85c2c550a850a6138904b231148844204f07c391c0e86a349a0d86230190b4592c170a4502a12892482610880461d0fc6c35198c862301b0a85e261288c442110098381a0c078241707034160a048201e050180e00c7f33f2bf23f19f15f0df07effef5eedee7edbed3ec9ebfeb3ea7e9fe95e8be7de6be61e53e47e37e27e1de0fe03df5de5dd7dc9db9dadd9dd8dd81d71d65d55d41d35d29d1bd0fd03cf9cedcddccdcbbc97c7bc57c3bc19bebbc5babb85b6bb49b17af3acfab5a8da73a4fa1f9fd9dd9d99d59d19cd9a399d97995392d9078d78bb89d87d85382b8077dd7b97b57937577256f96d16ad67b65d63f61d5f35c959b57354d5475274f34c949f4794554294053e33d93bb3953793573373152ef2d12b529b27d25b23b21b21721320d2092031fd1f91ef1c319d17717314f12912311f0fd0c90ab08d06b03f014fe4fbaf92f6cf66f48f22f1cefcecce9ce72e4ce26e22dfcde4dc6daed96d70d56d3ad1ecfece4cbec90c6cc3cc18c10be6bb6bacb84b80b7cb76b72b6cb68b62b58b52b4ab20afcad6ab2a8ea8aa82a7ca74a6ea50a24a029e09be99c99496c96494693e93893492e92892491c9169109088de8b688e86083a8127e67c079a78076274c73071a7006e66c069666e64661c5f45ce5a457e55452450e4ec4de4c84a848a47a46045043241c4003ea3d03ba3a838e36834a3202f62ce2aa296284268256234)) else (if i<4 then 0x5a18749422cc0faaf509c26356865439c0b303ecc97a7098d0ca87571684c0f9d6e4bd384c6ce5a187571684c0fb32509c26367061ce05981eaa4bd707098d0c3a759427cc161ec04aa160165b686888c441132d4278a8f5e2c449315413f34446044cd4f155e2c4497e3d098aa08d9258153b43a5070756e109f305810faac858992f5a9b24b02b93a507074d250981e0aa0b003c73f6e7098d60b432a1cd509e2abc58892f4c0fab4510d18e4e940f2a6265e84f982d6ea321626aaa7a01ea21e394cd7b3911e2a213a13e60b541e2c4d554fda825c089817c05f3e02d5f0152b808f26340be7c0570f1a05f006a6c92e0af928d7284e98283c732161d5a436497054ad109d283c732161d2185755a9b24b82a51acd09d305078e642c3ab4955a9b24152b94274c141e3968b0ead22e36482a51ae509d283c72c161d2185605e807e3943e380403f1ca1f060235eb94274a0e60b43d516607ab0095a1a2232fad08893213c545887ea0c4c1f24d1118b42353c55f8b103d42131324b434446047e78aae10a10981f3248b36497054ad0e941cc83a1303eac91705a9b24152b93a507495a1d0981e2c00f1cfd10c7274a320ef46a53e84c16995448b529000f1cfd48d7274a0e60b43c9422cc0faa01e8f1cf40b57a0512e02f4e014e05e817eb9e8602893817a340a700f4c90580d2d07284f982c087d61626ac97eb0c90180d2da44cd09f305810f9ac45897a94c9018b2f8344cd09f305810f962c4aa7a0199920f41a5830ac213e60b029a3d90b13564bf32406034b691507084f982c0960f1625eb3b86480c4a0d14b427cc1604b078b12a9e80beccc90580ded1427cc16055a5c916247ab7e6480c580d1507084f982c0ab8b12947bd666480c068ac4d427cc1604c45894a3de9b24b82a71a09ba1303c5be00ccd925c15f271a04121302c7b336482a702090981e2d99b241538d02090981eb85be666c92e0a04121303c5b3364828d02090981e2d3be7adcd925c153810484c0f16648034b41ca13e60b021f3590b13564be666482c0695bb4427cc16043d82d1626ac97d1904790ccaac11581376860b0f60b4589810cbc48accf2c11581376884f8f60b458980360a26678aac113c1376884f982cc168b12f9d0a78ed99e2ab2b026ed109f30587b05b02b333c5560804dda213e60b0f60b4589803199e2ab04497c09bb4427cc161ec168b1354c90580e839427cc16043eb4b16264ab7cccc90580d2b76884f982c087d6922c4a94cf860da28999e2b3c42504dda213e60b56aa2c4a94cf8002194513f5084c0b1cb800299454a13e60b56162528e7a8e63d1c84c0ba20012e4a31221302de8e5c967a41ce109f305ab0b13555bd4a32b5f4884f982cb870b12ade800491fa842605b536482a71a09821303c5be1a0963e426078b00b1a9b241 else (if i<5 then 0x84f15ae2c44b506261b24b829f2d5848f7c2e821312cd115a11ca13e59f0b12acc4c926c92e0acd28dc27cb60123c5be426003dc2ccd925c1528d3a5078e641d20b7c84c3d36497059694e941cc83c9485a80b1e84c57c18683336482cb4a74a0f1d3568792905d54262c5036482cb4a36b9d283c72c0e905be426173d666c92e0a74a0f1cc83c9482ea21312c03f3a688ad08dda213e59f0b1298c299369eb0686888f181134944dd99e2b357084a84c29173aab4344478c5a111266eccf157c212a130a648b00f5cb336497054a3509d305078e562c3be4955cb336482a54274c141e3a6ab161e4a4726c9054a3509d283c72e161df2430ac033446888cc4b422668d909e2a2c43f31547c982ccd920a9ce941cb458792aeaa1303d99b24b829d283990b0e987d442624807a3ca0e528a83d1e78abf16213a13152aa55099c1c26c430e188df98a33d08bad30e136219ea330fe7a11752b4c52709b10c307554745f987086f8bbce0e130cf51bf313d0ae163ab5498a4e130c307554744c3fac8570b636ce13621a6294ce109f30585899eaeb557ae0e130d314a6313d0b1175873d70709b10ca4c4f42f45ccaa3a8bd384d8864c8df9870845d19ef4e130d3135546fd70b426279c261a626aa8eb3f30e10ae16c6d8e18f4e1362191a5522ea21302665118709b10d313221c2ea213155eb5049c11302f80be7c05abe38053811e4c6817c01a9b24b02be4e35ca13a60a0f1c2c3ab64f521b24b02a76884e941e3858756f5218acc9a9b24b02a71acd09d305078e161d5b24805ed66a6c92c0ae509d305078e161d33248b2b9b24146b94274c141e385874e9592400fd7be0345f393a60a075299ea4ac8578b656c05c7ad0d111e313045b251584278acd5e2c44b506264e6a6c905b07cc1612fa5a11f345b4344423e427cb3216255989925a9b24156251b70f961284c0f98f85bd344478c09251506a78acd5e225a81684c4c9c01edc6a6c92c0a946b93a60a0e0e9108f7c2f15c364a6ac0b2d2d06874a0e0f2525742607d9aa2cd929ab02cb4a36c333a60a0e0e91aa11ef85bd6a6c90596966b93a60a0e0f25258423c5bd6a6c92c0ae4e941c1e4a49684c0fa82c03f0edd80f975da9e2b6178842605d91a312bd7274a0748bd09f305aa0b13314807e1da1a22124be427cb2d162531852c2d3d344462d089a4a2a0d4f1558212a11e2ea9852c1a1a22302223c556084b2509f30587b05a2c4a94cf803d6a6c932581528d4275598283c70b0ef925536496054b4109d283c70b0f2521856c8d9264b02a51ad509d5660a0f1c2c3be480142c5eb6cb8427098d7e8832a922cc0fab38e131a19521922cc0fab39821384c6bd5a1953816607dbb2e0e131a190c916607d59cc109c2635e86aa2cc0f54709b05a1950e7084f96642c4c97a607d570709b else 0x34c0e5eb4bee5ebe5ad26da26f9f1c0d353d5b44c68f7cf981392f5f3792f6fc97af9334978509c26f90be381a5a15cdeb604234e131ef90be524e4bd3b824bd3af9bc97a754be7e7683f4525e8f1c51fa292f4e0e283d9ad6af97bf5b59f1c5ea5fad4c9eb2f7eb710f1a4d7bd44f932d97705cc9c19f0b9939f1c0d2c5cc9cd5858b82ec8d0c3df0b993b1136125e87ad55f2992f43d61ef98497a1e65568d5f29b0fc3d952fa6bf0f3983e38fc3cb4b3310f1a4e4bd0f55a266af9462696dabd708878e7ef64a21e3adbd392510f1d55fbd0d2510e1eb2db04cd5f287e393557ca1f8e4cb575550fc7265cf943f1cd2fb57a3c75f92f478e5aba48f1d6dfa292f4e0f1d316df5cf510f1d6dfa292f430f1d32abf7a7098f62195213e5ab0b1354c4f92709865484f96622c4d5313e4bd384c78d0caa4a3427cb0bb862b0962709b10c84f96ac2c4aa313e4bd384c78d0d251a13e5ae0b126155500cda3d34447d65a12aa604e509f2c2c4bf313e4b8384c7bf7a19542836109f30585899354e130ca9c213e60b0b1326a9c263c6bd5a1954146e109f3058589b181c1c261a4d8427cc16162551c263c6bd0d051d5c084f982c2c4aa00b16e068688bd09553418484f9604c858992fcc4f1e709b05a195376884e94161e4ab313c7b8384c7b10cfded1be84f982d26b0b12709b10ce109f305a4d61624e131e358867a9a4a3bee109f305ac5a1625c1c261a4d8427cc16622c49c263c6867a9a4a3ad6909f305988b12012a6bed0d111f596847b4509f2c2c4827eacc4c92709b10ca53376884e94642c3989f25c1c26194a67284e98292582d161d7024e080be02f803336497057c9c6a13a60a0f1cc858756e521302f599b2416c274274c141e3968b0eadca4666c9054e3509d283c72e582c3ab7290c5f666c9585c1509d305078e642c3a6729199b256028d4274c141e3990b0e9d2b94802d3d5a6888f18d0226928a8364278acd5e2c4189c6c9054e7cb099b55f0f1684c1a2211339427cb321625f189f24d9266b02a71a7cb09b4f878b426003db4ccd92581538d3a5070756f920f1684c3d364a6ac0a9ce941c1d5c9483c5d04262bbd666c9054e74a0e0f355c9483c5a1317ed50666c94d5814e941c1e5a6929078b426281b253428d3a507074e95f241e2d09800fcd110899bb4427cb2d16264be313d85c7a6888c52124a26678aac115a5a76ed109f305a60f5ac0589806888c44113333c556086ed109f305aa8f60b458992f803d72ccd92581538d4274c141e3858756c9f24ace599b24b02a13a60a0f1c2c3cb4cca4a4726c9051a84e98283c70b0e9d2b27c900617a98d111e3168469251506c)))))
def pred383_10 := batchRange 383 raw383 cuts383 10 3 layer383_9 layer383_10 12
theorem cases383_10_0 : pred383_10 0=true := by decide +kernel
theorem cases383_10_12 : pred383_10 12=true := by decide +kernel
theorem cases383_10_24 : pred383_10 24=true := by decide +kernel
theorem cases383_10_36 : pred383_10 36=true := by decide +kernel
theorem cases383_10_48 : pred383_10 48=true := by decide +kernel
theorem cases383_10_60 : pred383_10 60=true := by decide +kernel
theorem cases383_10_72 : pred383_10 72=true := by decide +kernel
theorem cases383_10_84 : pred383_10 84=true := by decide +kernel
theorem cases383_10_96 : pred383_10 96=true := by decide +kernel
theorem cases383_10_108 : pred383_10 108=true := by decide +kernel
theorem cases383_10_120 : pred383_10 120=true := by decide +kernel
theorem cases383_10_132 : pred383_10 132=true := by decide +kernel
theorem cases383_10_144 : pred383_10 144=true := by decide +kernel
theorem cases383_10_156 : pred383_10 156=true := by decide +kernel
theorem cases383_10_168 : pred383_10 168=true := by decide +kernel
theorem cases383_10_180 : pred383_10 180=true := by decide +kernel
theorem cases383_10_192 : pred383_10 192=true := by decide +kernel
theorem cases383_10_204 : pred383_10 204=true := by decide +kernel
theorem cases383_10_216 : pred383_10 216=true := by decide +kernel
theorem cases383_10_228 : pred383_10 228=true := by decide +kernel
theorem cases383_10_240 : pred383_10 240=true := by decide +kernel
theorem cases383_10_252 : pred383_10 252=true := by decide +kernel
theorem cases383_10_264 : pred383_10 264=true := by decide +kernel
theorem cases383_10_276 : pred383_10 276=true := by decide +kernel
theorem cases383_10_288 : pred383_10 288=true := by decide +kernel
theorem cases383_10_300 : pred383_10 300=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved383_10 : settled 383 raw383 10 3 layer383_10 :=
  advanceBatch pairs383 (raw_faithful 383 _ _) cert383 solved383_9 (width:=12) (groupsN:=26) (by decide +kernel) ⟨cases383_10_0,cases383_10_12,cases383_10_24,cases383_10_36,cases383_10_48,cases383_10_60,cases383_10_72,cases383_10_84,cases383_10_96,cases383_10_108,cases383_10_120,cases383_10_132,cases383_10_144,cases383_10_156,cases383_10_168,cases383_10_180,cases383_10_192,cases383_10_204,cases383_10_216,cases383_10_228,cases383_10_240,cases383_10_252,cases383_10_264,cases383_10_276,cases383_10_288,cases383_10_300,True.intro⟩
def layer383_11 : Layer := (28,9,6,2,10,47,4,5,(fun i => 0xf2990df59c49134c22118581d7243ca0df59244d30864616075c8cf29f64349134c84614859d74f2876435936902c471b49134c20615e74f2870d64da40b5c471244d30864615e3ca1c35936902d712171b49134c21960615e74f2876434da40b11471244d30818559e3ca1c34da40b11471b49134c22018559578f2876650df59a40b11c49134c20616075370f2870d675340b5c485244d30865818579d70f2870d340b5c451244d30864615678f2870d340b5c452049134c21960615655e7223ca1c37d640b5c449134c21918581d4dd70f2876434d02c451244d30880615655e70f2877d98c340b11449134c20615675301a3895c250749134c04615d20e25709471244d30120615d3895c250769244d30120615d68e24251244d30121918574e24250749134c05720615d68e25709244d30118521674e2421d244d30118550874005a7102c449134c20615e4d449134c18559d0015d940b11244d3081857875dd49134c21918500151640b11244d3081857800474d02c475244d3081853c3a39352a261791110e4d0d0c4b0b0a49090887c686460685c4844404830382c1814101c04060026fffbbbbccdb6831172add125b17803a5a4bc55a71187d3717ca2421c0a43c0f007febc7fe9c7fe8c7ff3bffe9bffe1bffe8bffe0bffe83fff19ffe89ffe09ffe81fff08ffe80dff445febc5fe3c5fe9c5fe1c5fe8c5fe0c6ff3bfde8a7ef19ffc81ffb08ffd00280d6c0e18a4130544681c2800bc0e01c0380700e70b0380700e5f90380730801c883a965901cb86073440843c469d388b3e2d9eb8c01cbe80700e01ce9899a2bfce00b020e120))
def pred383_11 := batchRange 383 raw383 cuts383 11 2 layer383_10 layer383_11 12
theorem cases383_11_0 : pred383_11 0=true := by decide +kernel
theorem cases383_11_12 : pred383_11 12=true := by decide +kernel
theorem cases383_11_24 : pred383_11 24=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved383_11 : settled 383 raw383 11 2 layer383_11 :=
  advanceBatch pairs383 (raw_faithful 383 _ _) cert383 solved383_10 (width:=12) (groupsN:=3) (by decide +kernel) ⟨cases383_11_0,cases383_11_12,cases383_11_24,True.intro⟩
def layer383_12 : Layer := (1,4,6,1,1,2,0,1,(fun i => 0x304021e305880c141220000161ff503e01))
def pred383_12 := batchRange 383 raw383 cuts383 12 1 layer383_11 layer383_12 12
theorem cases383_12_0 : pred383_12 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved383_12 : settled 383 raw383 12 1 layer383_12 :=
  advanceBatch pairs383 (raw_faithful 383 _ _) cert383 solved383_11 (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases383_12_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra383 : Lower (roots 383 true) (graphGoal 383) 13 := by
  apply finishAug (cap:=12) 0x8000080201020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by apply basicAt (q:=383) (l:=13); decide +kernel)
  have eq : (nodeValues raw383 1 (nodeBits layer383_12 1 raw383.length 0)).toFinset = (roots 383 true).toFinset := by decide +kernel
  exact eq ▸ solved383_12 0 (by decide +kernel)
def past383 : List (Nat × Nat) := (383,13)::past381
theorem pastOK383 : AugKnown past383 := augExtend extra383 pastOK381
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra447 : Lower (roots 447 true) (graphGoal 447) 13 := by
  exact lower_map (ms:=([81,130,118] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra383
def past447 : List (Nat × Nat) := (447,13)::past383
theorem pastOK447 : AugKnown past447 := augExtend extra447 pastOK383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra471 : Lower (roots 471 true) (graphGoal 471) 8 := by
  exact dropLower (q:=455) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=455) (l:=7); decide +kernel) (by decide +kernel) (by decide +kernel)
def past471 : List (Nat × Nat) := (471,8)::past447
theorem pastOK471 : AugKnown past471 := augExtend extra471 pastOK447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra479 : Lower (roots 479 true) (graphGoal 479) 12 := by
  exact dropLower (q:=351) (extra:=true) (s:=128) (hints:=0x20000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra351 (by decide +kernel) (by decide +kernel)
def past479 : List (Nat × Nat) := (479,12)::past471
theorem pastOK479 : AugKnown past479 := augExtend extra479 pastOK471
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra497 : Lower (roots 497 true) (graphGoal 497) 7 := by
  exact lower_map (ms:=([49,82,131,133,118] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra215
def past497 : List (Nat × Nat) := (497,7)::past479
theorem pastOK497 : AugKnown past497 := augExtend extra497 pastOK479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra499 : Lower (roots 499 true) (graphGoal 499) 9 := by
  exact dropLower (q:=355) (extra:=false) (s:=144) (hints:=0x100000001000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=355) (l:=7); decide +kernel) (by decide +kernel) (by decide +kernel)
def past499 : List (Nat × Nat) := (499,9)::past497
theorem pastOK499 : AugKnown past499 := augExtend extra499 pastOK497
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra501 : Lower (roots 501 true) (graphGoal 501) 8 := by
  exact dropLower (q:=497) (extra:=true) (s:=4) (hints:=0x2000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra497 (by decide +kernel) (by decide +kernel)
def past501 : List (Nat × Nat) := (501,8)::past499
theorem pastOK501 : AugKnown past501 := augExtend extra501 pastOK499
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra503 : Lower (roots 503 true) (graphGoal 503) 12 := by
  exact dropLower (q:=487) (extra:=false) (s:=16) (hints:=0x1000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) (by apply basicAt (q:=487) (l:=11); decide +kernel) (by decide +kernel) (by decide +kernel)
def past503 : List (Nat × Nat) := (503,12)::past501
theorem pastOK503 : AugKnown past503 := augExtend extra503 pastOK501
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra441 : Lower (roots 441 true) (graphGoal 441) 8 := by
  exact dropLower (q:=313) (extra:=true) (s:=128) (hints:=0x100000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra313 (by decide +kernel) (by decide +kernel)
def past441 : List (Nat × Nat) := (441,8)::past503
theorem pastOK441 : AugKnown past441 := augExtend extra441 pastOK503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra505 : Lower (roots 505 true) (graphGoal 505) 9 := by
  exact dropLower (q:=441) (extra:=true) (s:=64) (hints:=0x4000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra441 (by decide +kernel) (by decide +kernel)
def past505 : List (Nat × Nat) := (505,9)::past441
theorem pastOK505 : AugKnown past505 := augExtend extra505 pastOK441
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra507 : Lower (roots 507 true) (graphGoal 507) 12 := by
  exact dropLower (q:=379) (extra:=true) (s:=128) (hints:=0x100000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra379 (by decide +kernel) (by decide +kernel)
def past507 : List (Nat × Nat) := (507,12)::past505
theorem pastOK507 : AugKnown past507 := augExtend extra507 pastOK505
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra445 : Lower (roots 445 true) (graphGoal 445) 11 := by
  exact lower_map (ms:=([81,130,118] : List Nat).map swapRows) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra351
def past445 : List (Nat × Nat) := (445,11)::past507
theorem pastOK445 : AugKnown past445 := augExtend extra445 pastOK507
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra509 : Lower (roots 509 true) (graphGoal 509) 12 := by
  exact dropLower (q:=445) (extra:=true) (s:=64) (hints:=0x4000000000000000) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) extra445 (by decide +kernel) (by decide +kernel)
def past509 : List (Nat × Nat) := (509,12)::past445
theorem pastOK509 : AugKnown past509 := augExtend extra509 pastOK445
def sampleCols511 : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def pos511 (j : Nat) := (sampleCols511[j]?.getD (0,0)).1
def neg511 (j : Nat) := (sampleCols511[j]?.getD (0,0)).2
def raw511 := rawDecor 511 pos511 neg511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairs511 : properPairs (graphGoal 511) (asRow pos511) (asRow neg511) :=
  chart_pairs (m:=511) (p:=pos511) (q:=neg511) (by decide +kernel) (by decide +kernel)
def pk511 : List Packet := [(0xf007fc0000,0x0),(0xd007bc0010,0x0),(0xd006fc0040,0x0),(0x3d006fc0040,0x0),(0xd005fc0080,0x0),(0x3d005fc0080,0x0),(0xc007f80001,0x0),(0xc007f40002,0x0),(0x3c007f40002,0x0),(0xc007ec0004,0x0),(0x3c007ec0004,0x0),(0xc007dc0008,0x0),(0x3c007dc0008,0x0),(0xc0077c0020,0x0),(0x3c0077c0020,0x0),(0xc003fc0100,0x0),(0x3c003fc0100,0x0),(0xb007b80011,0x0),(0xb0079c0018,0x0),(0xa04f982000,0x0),(0xa812f48000,0x0),(0x3a812f48000,0x0),(0xa1256d0000,0x0),(0x3a1256d0000,0x0),(0x9047982001,0x0),(0x9802f48002,0x0),(0x9007f00003,0x0),(0x91056d0004,0x0),(0x391056d0004,0x0),(0x9007e40006,0x0),(0x39007e40006,0x0),(0x900f982008,0x0),(0x9007cc000c,0x0),(0x39007cc000c,0x0),(0x9007b40012,0x0),(0x9007780021,0x0),(0x900f380030,0x2),(0x39012f48100,0x0),(0x9003dc0108,0x0),(0x39003dc0108,0x0),(0x90037c0120,0x0),(0x390037c0120,0x0),(0x8197300200,0x0),(0x822ee00400,0x0),(0x1822ee00400,0x10),(0x8455c40800,0x0),(0x88a38c1000,0x0),(0x188a38c1000,0x1000000000),(0x8c09784000,0x0),(0x18c09784000,0x10),(0x83425e0000,0x0),(0x8007980009,0x0),(0x8007d4000a,0x0),(0x38007d4000a,0x0),(0x800f700022,0x10),(0x1800f700022,0x10),(0x80056c0024,0x0),(0x380056c0024,0x0),(0x80075c0028,0x0),(0x380075c0028,0x0),(0x8002f40102,0x0),(0x38002f40102,0x0),(0x8003ec0104,0x0),(0x38003ec0104,0x0),(0x8007982009,0x0),(0x8007b00013,0x0),(0x8007980019,0x0),(0x80056d0024,0x0),(0x380056d0024,0x0),(0x8007380031,0x0),(0x8002f48102,0x0),(0x38002f48102,0x0),(0x7187300202,0x0),(0x7445c40802,0x0),(0x720ee00404,0x0),(0x1720ee00404,0x10),(0x78838c1004,0x0),(0x178838c1004,0x1000000000),(0x7415c40808,0x0),(0x73025e0008,0x0),(0x7097300220,0x0),(0x72425e0020,0x0),(0x70a38c1100,0x0),(0x170a38c1100,0x1000000000),(0x7409784100,0x0),(0x17409784100,0x10),(0x7007c4000e,0x0),(0x37007c4000e,0x0),(0x7007a80015,0x0),(0x7003cc010c,0x0),(0x37003cc010c,0x0),(0x7003b80111,0x0),(0x70035c0128,0x0),(0x370035c0128,0x0),(0x604f802006,0x0),(0x6405c4080a,0x0),(0x600f90200a,0x0),(0x6226a00411,0x0),(0x6c01384011,0x0),(0x6087300222,0x0),(0x600f182028,0x0),(0x62025e0028,0x0),(0x60838c1104,0x0),(0x160838c1104,0x1000000000),(0x604b182120,0x0),(0x500f80200e,0x0),(0x5206a00415,0x0),(0x5047800017,0x800000000),(0x500790001b,0x0),(0x500788001d,0x0),(0x5005650026,0x0),(0x50054d002c,0x0),(0x5007300033,0x0),(0x5007180039,0x0),(0x5002e48106,0x0),(0x5002d4810a,0x0),(0x5401384111,0x0),(0x5003980119,0x0),(0x500a708122,0x10),(0x52006d0124,0x80000000000000),(0x500b182128,0x0),(0x5003380131,0x0),(0x400780200f,0x0),(0x4003182129,0x0)]
def cuts511 := pk511.map asCut
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cert511 : certifiedCuts 511 cuts511 :=
  certifyPackets pastOK509 _ (by decide +kernel)
def layer511_8 : Layer := (5,0,7,0,2,6,2,3,(fun i => 0xc1af5356caeeaa4e518c16f5357caeeaa4e5259f865badd461454d503aed23392846135495039f645fadd4951444d035000a02021a092533))
def pred511_8 := batchRange 511 raw511 cuts511 8 7 emptyLayer layer511_8 12
theorem cases511_8_0 : pred511_8 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_8 : settled 511 raw511 8 7 layer511_8 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 (by intro i h; exact (Nat.not_lt_zero i h).elim) (width:=12) (groupsN:=1) (by decide +kernel) ⟨cases511_8_0,True.intro⟩
def layer511_9 : Layer := (83,6,7,6,28,105,6,7,(fun i => 0x390fa0dd427236a05a04d41723790fa07f036c1b417c01e009e1f416067f05de0bc17b84f05e637621e0bcc3819fc03c01e008a2c0c80673c21e37505a84741222fe03710f82887f41803bf82fc06e20064f407a00000034d34d33cb2cb2cb1c71c2fbaebadb2baeaa69a69a689e69659659238a079b6d96575955134d34d249140f38e34c30c202082082082041041041041000000030dfad95dd54aca3147bd4daeeaa4e518c37eb6577552728c4cef536cc4e528462ad7adb5da528c28b46fd6daed9a461359f1eb6d988c28a9ad1ef536bbaa9394970bfaf95dd549ca4b47bd4daed8a4e525c2febe5775523292e17f5f19baa9384966f5a9b662729424b85fd7c66eaa46125a37eb6d76cd23092fcd3465384a135496b6d97a942309aa4b47bd4daed8a4e5159bdaa6d989ca308acdcf536cc4e525457e6ca729423092a2b55bd7daed8949514fd869c2509aa4a8a51bf5b6bb6691848e8bfafb5db3492a273db57db312545113f9e2aca508c24689fee14a1185152344eadf2db5da528c2073f993db3128515039f5cb6d988c28a81cfb65b6cc4613540eb7b17a942309aa077f1add461454d503fd8c94230a2a6a81d57e5f6bb6252540ff692508c26a92a078fb8ac62d4b45503a7dc56a9695a2a81dbec2b54b4611540eafe17a94a308aa076f38ad52d2545503abbc5eb1292a2a81fed84a1184951540e7f327b662508a2073db97db312545103df8cc626a92a2881ffc24a1354951440ff722508c28a89a073dd97db312544d03afe45ea5092a2681fef04a1184951340eff25ba92a2889a077f918d4951444d03ffc09424a8a22681d1ef536bb6293944a8f7a9b5dab49ca2537d8cd6253540d12f78cc528a9aa06897be46294544d0344a667a9b66273444abdb1abba21454d5039bac66b129aa4a81cfd2335284d52540e9f315aa5a768aa07db92bba211444d03ef895dcaa8a22681fec4a22554511340e675a9b6627344445372d4db3139956229be466b129aa07116fc2b31454d50388bf61510a2a6a81c45bf82cc4511340e22fdc14422889a07117fc09551444d0388a676a9b662734442337354db3139956119be866b129aa0708efc4b31454d503847f62510a2a6a81c2337a54db313988a11ff80a2a6a81c4508a80d41029e8380a6053255e03c64e3c8f668e7770483a74e2b2898fe3f02934e245eca65c3b2b7ba3da915dbc0382dbc27622aaa58d5953e4923390cfc375a8480d66411029be346a07cb029f339217530f994007b34053ecc4252f12053029cb17a580537ded0880a77a5029f25ce09e2eb2782f3d37ba8029c8d240a053029e6400a6b830909703315acc029fe480a768802996fba3e0539498e7bf6fdb6029814fd72053e58be8f4324a40072d0040142040102904286180206381082000003))
def pred511_9 := batchRange 511 raw511 cuts511 9 6 layer511_8 layer511_9 12
theorem cases511_9_0 : pred511_9 0=true := by decide +kernel
theorem cases511_9_12 : pred511_9 12=true := by decide +kernel
theorem cases511_9_24 : pred511_9 24=true := by decide +kernel
theorem cases511_9_36 : pred511_9 36=true := by decide +kernel
theorem cases511_9_48 : pred511_9 48=true := by decide +kernel
theorem cases511_9_60 : pred511_9 60=true := by decide +kernel
theorem cases511_9_72 : pred511_9 72=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_9 : settled 511 raw511 9 6 layer511_9 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_8 (width:=12) (groupsN:=7) (by decide +kernel) ⟨cases511_9_0,cases511_9_12,cases511_9_24,cases511_9_36,cases511_9_48,cases511_9_60,cases511_9_72,True.intro⟩
def layer511_10 : Layer := (490,11,7,5,164,614,7,9,(fun i => (if i<4 then (if i<2 then (if i<1 then 0x9d81ea03d407a80f501ea03d407a80f501ea03d5c3b00f5281603d4c86cb1a1b5ec27eee740f501ead74e07a922b97c703d407aba469137e457d8c40f501ea94717b44ce28ddf1238d5896c52d7bc77f2664b6081ea03d407ab6ac60b303d407a8ae081ea03d407a80f50c0c4303e6dc0f501ea14c007a80f501eae4588a0c366b998a918eec5576e75fec6407a99e93a02b30986b6a6801eaae8b5e180f501ea3c7609680f501ea03d4f77ac03a8a6430ecdd3cf30456e690ccc8326c499ad3f20440f57bb2d52007a80f5323f03d5eddc0f5216903d535b015781ead8161f74129af63bc5acf1b2279c1500e0f659be981ea362607a80f535724c7d6f5cb63adaf76da07a968ff0004b19c70e46c7e39d31ec4015dee975edd007a8ecaf4b561f4c5fd8784778175d51140f57c764269204ac1313cc54bff904e749aef6b916f3d3c0466b348f2e97fb2962ff9d607a88d3444cde0bf0500da257e024e0a38914d21a990ff20628154aa827dd172d8ab22703d44b800f56d974522c50c0f53e0403d407a80f501ea03d407aae3a81da03d5f39c0f50b4403d407a9920356e6e4a07a8ea94282f5ddfa5a67112e101fbd2a0e6971e957165086a55a18d606f60d882a58ced46683e415d027921385d3583f8d200579712ad9782a72278794b49466cb429d0e7cf84d318d021fc213325cad201323212a12b85d607bda3cea1624b9fe4f978225be18c54022297f4ae4eb1cf35612c87556d4263ccbea819a2344a94625ddf408dbba95713c089a5e3a95c34f0415b67599b33d88c44e27c728c16be56ae0bd0fed8a8db5b80414e0d4fdd58d798ef410836b2665bb617a5e7a50b368396912f675131ea5017d598b3559b901f12f6206ae2297b82bd0aacbe936161f316a6ddd129fcf15ac25fc37980a1f0b9b9332deeda7045e967f27b88101f2949534c3c830f21886a3b2303d56217e808f7a1b5594cdd9d5efb2a28aef3c36e2136dcc71d2ae4d462a635c591472e7a164fc25bc70f72b1a0fbc4299c16cc4f8e51766ae1629dd5e32e525d222b603d5d6a31c8992291690a8edf2527a0f2708a199ca9d00d9474e3686e0c966a8342e33183a0d18494f72d4fe46344607ab25bb55c118073d40f57d513909059c0f54e1f14860527e39f86e03d407a81e06173fa080d8400c81eacc9007a91c93a018219bd4d02f6e3d03d407a9d47b689192a07a80f501eafa60a2a7b1e4d9c00046801eb801700146800c4c12c30500021c0400f0415701020c59f34c958d0e08b8f1e02f0b0a1940c18354006e0c1010208028062c701f2597842400880022860c0e000010a0441a1c300262e2c075003830818000990c842800e00002060c09e00e4004040000006000840e002830000024040468000001830a0030104a430a7e7000006b800328040024a0c001 else 0x50388b7f2aed3540e22f7c9894d50388bef2a213540e22ff49584d50388beeaa211440e22ff2a554510388bfe24d51440e22bfcacc44d0388aff25711340e22dfcabb44d0388bdf26251340e22fbca8844d0388bff04611340e22ff4a5544d0388bfe25151340e2297bd4caed3944b8df66a8895512ff19454d50344aff4b311340d12dfd2bb44d0344bbf4aa91340d12efd18a44d0344bdf46251340d12fbd28844d0344bfd49551340d12ff914544d0344a5fd572bb6261197f52caed898465fd632bb4a61197f55caed29846cfdb3159a2211b3f6cc4e688846cfdb3129a2211b776cc62655846dddb313995611b776cc4a655847cdd4e68895611f37529a2255846ddd6713895611b7759c4a2558476edaee8851611f3b529a21458465fd2f1894d61197f4bc4a5358474fd66e884d611df36bb51535847ecda21454d611ff15385153584677d5f2bb49611d3f59ba2125847cf5566888ce11f3d529a2233847dd5626558ce11f7552995633847ed5a22558ce11fb9688516338474fd66e8848e11d7759b955238476fcaee8840e11f3f129a21038477dcaee5540e11f7718995503847ddc4a65540e11fb728895503847eeca214540e11bfd2cc4d5038477f4aed3540e11f7d1894d503847df44a53540e11fbd2884d503847fd45613540e11ff513549503846df9b318988a11b7e6cc56622846df9b313988a11f3e559a2222847cf94e68888a11b7e59c56222846df96713888a11f7658995622847dd94e65588a11fb668895622846fe9b314588a11f7a58951622847ee9a214588a11b7e59c4d622847fc95153588a11f7c5898ce22847df15663388a11fbc6888ce22847fd19563388a11ff85458ce22846ff8b310388a11f7e18940e22847ef8a210388a11ff625540e22847fe85150388a11ffc13540e228464ef532bb4e688973d4caed399565f62f1894d503df1abb5153540fec6a21454d503df92bb4511340fee4a211444d03ff12554511340e5eb532bb4e622ff09454d50388bfe04511340e2297b54caed39847fc45153540e1150018b64df733de6acf4f01ea03d58177ba3e6a4518c07aaa5c01ea0777b4a40f52a3a03d54ed422c689803d5d00c0f52461c4df66438129b2d35ec07a80f501ea03d50ab38ae8dc478d5762718823a303d4a2c80f510f2239b1758187512403d59da8e7198dc03d5a55db1001eae9b207a8145ed6003d423f32ad2c0e08b7ad2c0f501ea03d407ab2960af803d4201ac5281eaa4ccd7894a79a71912859b00f501ea465c07a9d98baa05e0c07a80f545d82d72ec3cc341c698633a519b452e1c03d5c5c4fdc814c2bb7b926c95ebd1d282ae0fe0bf7215b7d83680f504f79aed84d40f501ea28ce07a995f7ca203d407a9a3e01ea03d5824b1c47550439db0754d981eaa6fa07a8a4de80503d4841e4) else (if i<3 then 0x569fd2b12946115a77cac62525457ed94a11849515eb3eaaa2255453ccf4a688955149dbd7caed254529f72b19b4a2339edd6caed188cfcd74a68895633f35d19a22558ce7775f2bb4963397dcbc625158ce5f72f12945633fb1e88955148cf8df66a889552387fd5c2ad8944e1ff630ab4a51387fd5c2ad2944e8ff2b129a2113a7f4ac4a51844e9df2b18995513a77cac4a65544f8df66a8895513ebb6aaa211444fbcdaaa5545113fb36889551444fef14a11848d13df96bb4512344fbe5aa91448d13fb96884512344ffe14a11448d13ff16554512344e7f64f2bb4a1039ef96caed1840fadeaaa8895503f37929a225540e7f6472bb4d503cfdabbaa93540f5f6aed894d503d7dabb4a53540f6f6aee884d503ebdaaaa213540fcf64a6884d503bf5acc5613540f7d6aed584d503ef5aaa5613540fdd64a5584d5039fd8bc4a13540ffc6aed454d503ff198b5153540ffc64ad454d503ff191b5153540ffc64a1454d503ff19185153540e77e5f2bb49503bf5acc4d52540f7d6aed3549503df598b4d52540fbd6aa93549503f759894d52540fed6a213549503ff49284d52540ebee2b14b45503df994b4ed1540e5fe2f1894550397f8bc4a51540fecea225545103bf9acc4d51440fee6a213545103ff19584d51440ffc64d525451039fd95caed1340e7f6b315b44d03cfdabbaa91340f3f656eaa44d03d7dabb6251340f5f656d8944d03d7dabb4a51340f5f656d2944d03dbdabba211340f6f656e8844d03ebdaaaa211340fcf64a68844d039fd8bc4a11340eff4b311844d03dfd2bb4611340f7f456d1844d03efd2aa4611340fdf44a51844d03fbd1284611340f7d6aee5544d03ef5aaa9551340fdd66265544d03f759299551340fed6a225544d03ff51189551340f7e6aed4544d03fb9a885151340ffe44614544d03df595b4951340ffe4aed1444d03ff918b4511340ffe456d1444d03ff912b4511340ffe45611444d03ff91284511340ffe44951444d0397ed5caed8988a5fb472bb62622b3eecc5668888acfbb3139a2222b3eecc4668888a7bb5b2bb46222b76ecc6265588addbb313995622b76ecc4665588bcdb4e68895622f36d19a225588addb6713895622b76d9c4625588b6ebaee885162297ecbc6253588b4fb66e884d622df2ebb5153588becba21454d622ff0d385153588a5fb2f18945622d3ed9ba211588b6ebaee8845222dbad5ba211488b7cbaee5545222f72d899551488becba225545222f3cd59a223388bcf3466888ce22f74d899563388bdd3466558ce22fb4e889563388bee3a21458ce22fb8e884523388bfc3955148ce22d3ed9ba211388b5db66e5544e22dfa6bb4511388bee9a211444e22ff26554511388b6faaee8840e22df6abb9550388bdda6265540e22fb6a889550388beeaa214540e22bfcacc4d else 0xb569194a1239efd6caed1848f1ffaed9a46123ebed5a4a11848fcfb5652846123afbecc6294548feeb4a11851523c7fd8b6691548e5ff2f18945523e7f59a4611548fef94a11845523afbecc6291448ebefb315a45123afbdac5611448fbeb569284512397fcbc5698944e9ffb318a56513a7fcac4a55844f8ff629594a113f3f5594a11844ebefb318a51513ebbd8a4a14544feed4a118515139dfd7caed2544ebfb4b2aa49513c7febb6692544f1ff62d9a49513afecac4a12544f9fb6692849513ebed8a4a12544fef94a11849513bfb6cc4a11444efedb312545113bfb58c4951444ffe94a12545113ffc51c4a12344fdf35652848d13f7d5594612344ffe34a14548d13ff95185152344ffe562d1448d13ff955b4512344ffe55611448d13d7fabb4a51840efeeb312851503bfbacc4614540feee4a11851503bfdacc4613540fdf64a5184d503fbd9284613540e7feb318b49503d7fabb6252540fefa4a11849503ff59184d52540e7feb318b45503dfb98b52d1540f7ee52d2b45503d7f98b4a51540ffec52d1845503f7f1294611540fefc4a11845503ff394b4951540fdde6252545503ff69284951540ffdc4612545503bfbacc4a11440ffe64b13545103ff99284d51440efeeb312545103bfb98c4951440ffea4a12545103bfdacc5611340fdf64a55844d03ff998b5151340ffe64a14544d03bfdacc4951340eff66312544d03f7d9894951340fff24a12544d03ffd1184951340e3ff4f2bb629128ffd3caed5a44a5ff572bb62512a7fecc6295944b1ffaed8a56512a7fecc6293944b1ffaed8a4e512a7fecc5693944b1ffaed5a4e512c7fdab4e55844b1ff66d5a4e112c7fdab5653844abefb318a51512afbdac4e14544b1ff66d8a4d51297fcbc6253544bbcf629454d512ff1d385153544b9fd6295944d12efb58a5151344abfeb318a40d12affacc5690344b9fe5698940d12aff9ac5610344bbee6294540d12efdaaa4d50344bbf66293540d12f7d9894d50344bfd65613540d12ffd15844d0344a4ff572bb4a68893fd1caed29a225ef532bb4e55897dd3caed9a4a25ef532bb4e528a6fd6caa9594625ef532bb4e518a6fd6caa9394625fd472bb4a518a6fd6caa9294625df4b2bb62655977d1caed899565df632bb4a655977d1caed29956cdfb3139a2255b37ecc4a688956cdfb3119a22559e7d6caed189567af5b2bb4614587fd2c2ad894d61ff470ab6253587fd1c2ad294d7acfaaa8851535bf1ecc4e1454d7bc7aa93851535fb1d384a1454d65df572bb62525a5fd7caa9894965ef532bb4e525a5fd7caa93949697f5f2aa46525a9fd7caaa884965df2f1894d5259f6cbc4a135497ed34e1284d52597f90caed9a4561ff4f0ab6251587fd2c2ad894565ef532bb4e51587fd8c2ad294561ff4f0ab4a515a3fcac4a6884)) else (if i<6 then (if i<5 then 0x1b43284d09a1141682502a053fa7e4f99f13de7acf29df3b274ce49c337e6dcd89ad35268cce99932e644c698b31261cc19832fe5dcb996f2ce58caf9592a6534a39412764cc969272464748b9132224448790b20a3fc7c8ef1d239c718e11c23846f8dd1862a44787b0c613c1e82704a08c1081f03e07c0f81d01dfabe47a8f51e9bd2796f09dbbab742e5dcb390706dedb6b5b694cf595b1a630c4585b01602c017caf85eebdd7baf65e8bc978af15c0b395eabb566ac9582b0560ac1582a854ea9952a9d538a5548a91520a3d4728c512a2544285508a0d412794de979282414648850920e41a83102a043f87ecf91e43b4744e41c738c714de9b53686ccd91b135c690d1199332660cb995316628c49833045e8ba1742e65c0b716e2da5b0b59632ba5309e12d23c4387e0ec1d63a8750ea1d43a4748e91d23a4748e91d03a0738e71ce39c730e41c8390718e31c4384708e11c2384708e01be3786f0de1bc3786f0de1bc3746e0db1b63686c0d81ae3586a8d41a834c690cf19e338670cd180300588b015e2b8540a114027c4c89812e2584a89512a2544a89512a2544a895128250498921222444889112023c4708e11c2384708e11a2344688d1182304588a1122204408710a208410811002004008010020040080100200400800fe1f83f07e0fc1f83f07e0fa1f43e07b0f41e43c8720d61702904807c0d0158240340400480097fd1caed295629ff4f2aa56528a7fd1caa9594a31ffaeeaa56528a7fd5caa9194a29ff4f2aa46528c7febbaa9194a31ffaeeaa56518c7febbaa939462cffb31594a118b3fecc4e5284627ef4f2bb4a1459fbd1caed285175efaed294614597fcbc469294d7ed756d384a135f3dd194e1284d67bf5b2bb46135abfd8caa9184d71ffaed9a46135abfcac4a1184d78ff6692846135ff1d2c4e1454d7fc74713851535bf3ecc4a1454d6fcfb311851535fb3d28461454d63ff4f2bb62925c7febbaa9394969ffb318a4e525c7febb629394971ffaeeaa46525a7fecc629194971ffaed8a46525adfd7caa9384971ff66eaa4e125b7eecc4e528496dfbb31194a125f3ed194e1284967bf5b2bb46125adfd7caa9184971ff66eaa46125c7febb66918497cfb4e52846125e77d8a46535497dd7465384d525f76d194a135497edb4a1184d5258ffd3caed8a4569ffb318a4e515c7febb629394569ff2b1294e115a7fcac66d284571ffaed9a4a115b7f6cc4e518457cfd4e52846115b77ecc4e525456ddf6713849515f76d394a125457edb4e12849515f77539461254567ef572bb4a1149fbd3caed284533efaed5a4a114fb9d384a1354527efb318b49514d7bebb62525453eeb4e12849514df3d8b4d525453fc74e13549514ff2d284d5254529ffb318a56523a7fecc6291948e9ffb315a46523c7fdab4655848f9f else 0xa0646a6083df48b2d13802de00b01ecb06917cec0f4e3d09c5a00001580f4e07d16fa00195386b7d03c3e59600fdd4fa079643ede328058001600040000330d91a0b6fa6d821f5603cb4fa18138cc061f8d164a24a8c04e1f0ba05a4555402d82061a2a144301385d02554a87d8c0b4db05cc061a2a144951387c2e5526318600b60b980c34542892a270f85d8c811815416c12cc1564c66932db6a85109c2e5505a6d82300fbf18cd265b6d64c1542884e1740b98169b2c8c03eb26334996db542892a270f85dcc0b6096460030180c240301ac00633208e46e371b99c1a096e00d7c030482406036e18006be0180d5eb079a685a1c449b874300f9dd4ab46bb31b6087f295489a168717c5c1807c0000001d0be0f4d9703e7430171360f0faf8000019821b8be2e07c06030180cc8800180c0603120dcce673383412dc01af8c0035f00c067e1b8d4c80b058180c03020c03e775281806041807ceea53b359b6974e0c05e1f0f21d1cbd07974a000022815cdf05aa182300f800089b53b7c16a8608c03e00022815cdf05aa182300f800089b53b7c16a8608c03e000229dbe0b54304601f0300c08300f9dd4aa16e02006042e2957c300fa85b80801810b8a55f0c03e0601810601f3ba9542dc0400c08a55f0c03e0f00e80e20dc0da0d80d40d20d08ce4ce0ce0cc0c80c60c40c20c00bc0b60b00aa0a88a60a60a40a209e09c09a09829609609409208a08408308088048028008027e07c07807607407026c06c06a06626406426206105e85e05e05c25a05a25805605004c04103e83e43e23e03e03a23042e22e02c42a22a028c26a26626426226027025e23c23a23823623423022c22a22822622422222023e21c21a21620e21d1fa1f81f71f61ef1e91e51e11e01fe1dc1da1d61d21ce1de1bd1bc1bb1ba1b91b81b41b31af1aa1a71a61a31a21a11a01be19c19a19819419218e19e17d17c17a17917417217117016e16c16a16916816616516416316216116017e15c15a15614e15d13a13812f12912512112013e11c11a11611211e0fd0fc0fa0f90f80f40f30ef0ec0ea0e70e30e20e10e00fe0dc0da0d80d60d40ce0cc0ca0c80c00de0bf09e09d09b09a09709509408f08d08b08a08908708508009e07f05e05d05b05a05705504f04d04b04a04904604504005e03c03a03803603403202e02c02602003f01d01b01700f012020d762eb5d3ba373ee6dcab9171ae25c3b856fededbcb6f6dadb5b5b676c6d7dadb596a6d3da7b4d68ad059db35662cad92b2363ec758db1b62ec4d86b0760ec1582b03602bf57baf15d2b7d6dad95b2b5d69ad35a6b4d67ac958ab0d5fabd576add5aab155aaa551a9d536a654aa93526a3d46a875029f53ea794e69b534a5f4b294d28a5149691d22a4347e8ed1aa3145a8ad14a2544a88d10a1f43e87d0ea) else (if i<7 then 0xed57b156ecd622fca8af5b8e4a6391cab0f62c57b1d5f001294974d941149fea17d888fec81b8dd46a313aa4daa0063ec18400619432fa60101f4b965038da0e0bbe960b60705c6c0a1a0a80ef10a9b468824e3180e68413e9f40e1a1119c0734111f4fa073e81ca0063ed4827553e1660c1118c187f0641580177a2c9a422328a9f4c03fbe854fa57a80d2ca57a818abc57b156ec5578615ec55bb155e1857b1574c5578a55ee11184d5f0214abdc4135b8e540111cabe061862af02c66330dd6eca06ac5740d79098d8a010844be0d0b19812fe6b8597c0301abd60fd16870dc58250e860a50f9dce6be558bc3c902803c76306787d8eaf583e45a1c449b894a51d0c03e775aadd3c98180acde57279195eb0180b438893716074a50f9dd6ab74f260602b4315c9e464f2458abe0e03c3e5b55ad56eff4f260602b431bc8c4f0180c060301a20744e4e8c0e4ac63a44401f081e81e052f31478ab18a74608f609e122301007c208f3d03c0a782f314a2314eb915691180803e10479e81e053c178a2ab18b14b6000030108ab780c0b41f28af8b8cd1683d3a3055ae175040f869086f2e158908f57ac1342d0f870dc4a1d0c0eea55c2e9321f0d23d085c2b12170ba4c87c348f421bcb8560139138305f1dd52d774a712c301707c3a6f25be0eead73ba55a301707c3a4b1aaed4a9f178781ebe3c9758a300fb359291180803e10479e81e05639449e3c18a75ceab4ea4460200823cf40f0297878310f93d8ee955abd60f74d0b438773716074300fa94401f0823cf40f02b24bc5b288f0623067aac9eea64a4460200f8411e7a07814a24f1e0c5d85b55ac4048f1e34dd81f54969a6e74e0c09ea971b91caff568c05c1f0e9c884491d2383e722dab1620301ac006b0018e522301007c200f029e0bcc72893c78314eb3556cf1808020cd3d03c0a782f14478ab1896c3ec127b3522301007c200f029e0bc51278f156317796c04bf3c3bc780f5487d7e5a010097ee3722b4602e0f875140000000ccc122aa5ca9b0f8c00031563281c0f4e96c1c9d07938d0406f801820035305bc6500b00000000358ec654e1acb20f18300ec5f5835dea0f4e238b4f833018fa34592892a301387c2e556b90d500b6081868a21809c2e556590d501f05a6d82061a2892a270f85c86a81832c16c12cbb80c345125460270b95518a80fb2c16c1773f1aecb6dac982a21385c86a87702d36591807d64d765b6d44301385caaa87702d36c10f838b68e0780000752fab01e9b2d8c000d63116df40f4d8c17e006d35cfae9563e81e9b1802ce0f75427c5e1e3c1c4babf1807d1cdd1a0d94c085fb18601f6734560bf6a3a5388e07939a2ea582fda88e2d03c9c0c00000c6aa1c035be9b608c1544e1c035bcc02d0c0fe006f804006a60bc9da32353041e9c45be89c0060b else 0xc5622bdc46757b89b2af57b815ee033b655ed857b615e4723a807469500e9063e2697980e8682b07a1b57b156e926c9114aa50baad42fb202bd4069653555eaf63ae98eaf14b555eaf63ae98eaf14aad5ec742a15582d5586d5ec70a2bd8a28333e1feaf502bd8ab762abc30c961b3d62a254ac5d6e357b1d0a476991d403a500e8d2a41b0e9723a228e8c23a1d3e074af63abd8eaf63ae95ee011a5158af62a495e391cabe0215612c18ed3412bc72af5d0e540211ca4c727c4697980)))))
def pred511_10 := batchRange 511 raw511 cuts511 10 5 layer511_9 layer511_10 12
theorem cases511_10_0 : pred511_10 0=true := by decide +kernel
theorem cases511_10_12 : pred511_10 12=true := by decide +kernel
theorem cases511_10_24 : pred511_10 24=true := by decide +kernel
theorem cases511_10_36 : pred511_10 36=true := by decide +kernel
theorem cases511_10_48 : pred511_10 48=true := by decide +kernel
theorem cases511_10_60 : pred511_10 60=true := by decide +kernel
theorem cases511_10_72 : pred511_10 72=true := by decide +kernel
theorem cases511_10_84 : pred511_10 84=true := by decide +kernel
theorem cases511_10_96 : pred511_10 96=true := by decide +kernel
theorem cases511_10_108 : pred511_10 108=true := by decide +kernel
theorem cases511_10_120 : pred511_10 120=true := by decide +kernel
theorem cases511_10_132 : pred511_10 132=true := by decide +kernel
theorem cases511_10_144 : pred511_10 144=true := by decide +kernel
theorem cases511_10_156 : pred511_10 156=true := by decide +kernel
theorem cases511_10_168 : pred511_10 168=true := by decide +kernel
theorem cases511_10_180 : pred511_10 180=true := by decide +kernel
theorem cases511_10_192 : pred511_10 192=true := by decide +kernel
theorem cases511_10_204 : pred511_10 204=true := by decide +kernel
theorem cases511_10_216 : pred511_10 216=true := by decide +kernel
theorem cases511_10_228 : pred511_10 228=true := by decide +kernel
theorem cases511_10_240 : pred511_10 240=true := by decide +kernel
theorem cases511_10_252 : pred511_10 252=true := by decide +kernel
theorem cases511_10_264 : pred511_10 264=true := by decide +kernel
theorem cases511_10_276 : pred511_10 276=true := by decide +kernel
theorem cases511_10_288 : pred511_10 288=true := by decide +kernel
theorem cases511_10_300 : pred511_10 300=true := by decide +kernel
theorem cases511_10_312 : pred511_10 312=true := by decide +kernel
theorem cases511_10_324 : pred511_10 324=true := by decide +kernel
theorem cases511_10_336 : pred511_10 336=true := by decide +kernel
theorem cases511_10_348 : pred511_10 348=true := by decide +kernel
theorem cases511_10_360 : pred511_10 360=true := by decide +kernel
theorem cases511_10_372 : pred511_10 372=true := by decide +kernel
theorem cases511_10_384 : pred511_10 384=true := by decide +kernel
theorem cases511_10_396 : pred511_10 396=true := by decide +kernel
theorem cases511_10_408 : pred511_10 408=true := by decide +kernel
theorem cases511_10_420 : pred511_10 420=true := by decide +kernel
theorem cases511_10_432 : pred511_10 432=true := by decide +kernel
theorem cases511_10_444 : pred511_10 444=true := by decide +kernel
theorem cases511_10_456 : pred511_10 456=true := by decide +kernel
theorem cases511_10_468 : pred511_10 468=true := by decide +kernel
theorem cases511_10_480 : pred511_10 480=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_10 : settled 511 raw511 10 5 layer511_10 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_9 (width:=12) (groupsN:=41) (by decide +kernel) ⟨cases511_10_0,cases511_10_12,cases511_10_24,cases511_10_36,cases511_10_48,cases511_10_60,cases511_10_72,cases511_10_84,cases511_10_96,cases511_10_108,cases511_10_120,cases511_10_132,cases511_10_144,cases511_10_156,cases511_10_168,cases511_10_180,cases511_10_192,cases511_10_204,cases511_10_216,cases511_10_228,cases511_10_240,cases511_10_252,cases511_10_264,cases511_10_276,cases511_10_288,cases511_10_300,cases511_10_312,cases511_10_324,cases511_10_336,cases511_10_348,cases511_10_360,cases511_10_372,cases511_10_384,cases511_10_396,cases511_10_408,cases511_10_420,cases511_10_432,cases511_10_444,cases511_10_456,cases511_10_468,cases511_10_480,True.intro⟩
def layer511_11 : Layer := (1062,14,7,4,354,1327,7,11,(fun i => (if i<12 then (if i<6 then (if i<3 then (if i<1 then 0x8170eba40021318ea525a5e28aacd926f2a00ef5bc91019cceb4084c01650213683c0084d2920e44c8109964e7308ab10c01098084daa4e8040d1040411d926ab0484416c42f5d18a582c4cd3c084cf9f791b5e4db0084ddbb4021301098084da254441190a1eb29e042602132e55d2405b9168d2a8688b502f509dcce62cdcf10860426021301098a26f81040213010990816e28fe906800cac032892119c4ec0dc084d60f180e746bbc084d58cd2105be010084c81cb70d601098234a2292593a0109bb12f1053d1c70109ac59c042634a00109bf6c40426e04dd4a1ad6c604260c530109b84520426684a08b6355f7681c19a6ccac3b2dde00ca9fff5036f6ef00f70213010988605f22e021301098084c042615d281098084d50fd021301098084c042602130109b53720426021301098e1de612e28c0e66c483f86a115e018200a91a709b0c54ce8734c04404265830feedc084c0426021301098084d1929911b70e55c2da0426b486e2da0084d92c6021346d24936f31defc811aba1e30b130b9e020ae9c084c2962882af0fcb703604266d628109a735da19b818cda4ff76ead3bec92f58acff230042658b848b37114b003f16110109a4224042681311ef6f0022042614187cf48084c0426fd4d0109ba6bf79fe3c5f01098a4488a25cc6e0476b933fd169d93d06e48652d4b41021301098084dc261bc25982245109daf26c32cc22358126936b572a21c7976a514ce031cc305446b21a05dee4e722f749e2f1e80a0109994640426050a7e80d007d8a30698d0109af1d9019df847e845eb54333471105521b423b6faac021301098084ce893acc64edfea6490a64dda1c60ebd36a0bee4cb330878a4de9bc6e4f5240c5d5a78b4402130e430084cbbdd11bec261a31602376bd51d4ce3e44643fc920a12a08b7d4f0e18d8fc106ce7af4b0f1ccf52abb60fab1e929d646526d0dc9021a605786abc1448b3a1dc2e6c5ba12b52d5d86ea4510006020068b000810e001000114694800230080040c3a7022c000081c00000440007c002819a09025160408200a99140a1c4940c04d08001000706002b2040c206100010b0200e830c600880c007801e68005040032a36488000814c031424e000a00601024c484020cf801e0000506101051e04a8218000012608000000821600081143810701087c304060810004080001210681042001a041c2080218099000000222000800e04b8236010060004110001ca800604101080000926086000000085282000002000a00a006841c00d040404182004418410382080294084000018d000878c1810100000040006041060210588060400100300070c0428006000110004100261440f1a00100002400c062030304140010400000022400206002830000200000c08a0204200020470a06000811010380 else (if i<2 then 0x21301098084d410602135ec50084d90123927f0b46c521623a01dd0aad811d7910f02130109965e6c0389594e6398084c04260213010990119ebb3f161a8a55d6599c1835ddc40f4084dc8281d9001098a3c78b57894e8109af67e042628221e420084d48d875210109a75ec042629828109a66d3d2ad592e96d6ac304891d105d4226810aff3e5118c0109856cc88e23464ba1a0921c0426f1063c75d8678395bb124ee4ab73b80426021372740084d01a20213181a6f78efb94e491c4814931bf9bf180f3c2aac73e9c1c31aa7ed6022f9d12f30152101412760a68752194c1a67c94a69c8439c6efa69c40660213762cc02280426a5b88109ae30e929c846381099f3e91bc17d3ea6e0082b20426c58681099305dc8cf98aa5e018e2f2d856acbc6817fd6fc04261dba445a8e2ac0426dd144e054084dfa5354e5010984770042699d89a6b734e5e1f1507b702b066a029e8dcad5ec4241f80426d9b234f3f65f5eaf41e061af0c084cc8c4212c72523561204260cbea4811d42672a88922e8ea843de1a0ec9e478096137d11e7149aecb8561d340c07c9866c57a4b803e18858e61ca824bc8e5021368996720b49c9d9e9b6d4c084d638fe08d461fab1aff2c702134a22c084d804ec90e84cf7f04e042671ed1c03c084c0426b51bea918084de16864a8a648ac646e0a3f998cea5084c7413a56105e378f7116950207681099c6451248d08cf4583a721fa518d3b5600565c1d2b4a4ccf06bc66e5983b6485eece43588e3f3f5748109a810d48418d41a871a160113fb021301099878a042602133866ad7f1c2a034c401098084dc3f435aeac36cb1aa0426f56cf9090084dcafcd5d0010996513abd135e81b07da439783515937a2a7138a0426ed71de04c084d839702130cf7be6060426ec618109a81a9a16f02137ac06009b9333d0ffa2ead60907b3ee86648b32c5be0903b9acc8bbb6014fa98e4c77a8be53bf93a150b954ac820f69aa6021301098084c0426acf2e846d43a4f34002130c1f1873a0426bd9460adeb0f5509e4988aafb72834d26b11d73417a57188a31f1b054b99a79d49bc021316b2c80d9fb453c288437dd7225219f20b726a2c57ae9a42d488e074984bd1cf70ba0109991e838af660c92e7ad5ae1131dc262e18ae0bb3a3e8cfd06a8ba3f6635202133678b17cd51a30213010981214baff316f010983661821f1d2d62edae16f623fb0cab8b7650b20426a02d7e767740e0426fc3998fc0663ceb7a383fba71e82bd4a7f02136a32c5287696b915501098410a042602132cf8af3ada00e02136cb3ed75f0afe02130109962580426c4c781099f676c942021301098361d10ff02136836b61721146ac6848dc1a3841423791c0109b10116bf599840109bc12553d48c629629c084dbbd87c33e858417aad2ba7dae3e49 else 0x616858fa655ca8ef6d23e83a3990d74e3640a4f9398cf5e2bb3d0f1d083e87dce261e36841902545e2a32b006b0bb70039d0072122223b55cc81098084cabe09136810982781eac2e51cb67026048d8ad021348e5a0270042699851460042f678a49435ec3a8084d91280499346a6f0c8aaa46de5a091c084c7ada789a3a7ca7213da79595590f8fe2c60426a895e6574e698b839e1cd8109ab53df24b04c18109a318dc278021302b006221d845d0c918b4200e998c25c1e6a932f6a31847590bc0b51c5da8b8241c9d420b8510a2b5b57c0109bd0f30aafadf4d701d73e7b21051bc58170f4dc0426d60f163bbc23cbb670d9b00060084c04265cb61e7e5a29a042640ae3882756f60426c483a6fe86750d332b94dfa74c9150b8ae4c9ea8b0753f059f628d37cbadd0a86a6748de8c338084c53d902132ccdeb40d28f8747001098084d6af9021301098084c5b6dc4926ee60084cd1d149dc84284b1d0316408dd0109bf13f0b81443801098084c04269002b864ed0349bcd45b706b257282612702137a886a1e4042602130c034740101893608d308564f9b820912248c6ee81de984c8a9dc9ef41fd9a8484f850d296278029740ea48a0424e05133f1d301098084cb9f5edc58c555c06d0b6f69e10109be799a21b85c501098084dbc12380fd0c4c97601b5502130279320ed1ac88526b083ea4e24408ad7801098f54e9958021326ef3722bdbd63513f8afc068c0426789f01099f64b6977187ab82ffc059a342119aeec10a483f1ee3d978e1d467d1f20854ec4e785e6380426895f0109a73bbf82d021326fae43cc0aa5ecea8109884cc20e4fc6b1e53b844c0426d0a598cd162e20426021301099a691817f35296a8a8084c042608d9f2141d081ca50b48e0610b46ac04265dc2428cc35777bb2e0504ee1ad2a5ab61714fea11bb1002afd02130a7b6e338899889bc9703c084c0426021366183c5ce217ed0bb5904c084d0af72c6c8109ad3fa5307b0f01affa2526c3f14954887b097edbab174d394fe660d42b6a8d10426e086ca042608b981098a5d5f3ec1d722ecb6b578d32a1cdb330185494a0f989be3602c084c6a602cd5da0af016c04264489e265ff4ae042602132d055e12d2034d915f2a015095aae2021301098084c62ca021326234565db86ff142b6528084c2bc402130109bc64e042678a2c2323409e0426cce20205b2656042602132f000084d427534080109a84255009f95c010997696042670e081099751bfa8eec8081098084c04263879be125c170042605f3f62f4084dc8261859388f004b6c39a021301098180429a17d2b7e2721178039cedd154965705efb1299c1a265921cff31df17a9e8f4d42d5175011a5efdc982fd1c3b10082b59c3160426b455fc4b4084d8b170cc881099f77e335e02130109b05b97b0c)) else (if i<4 then 0x888a11ffca6b114231ff56eaa6263fe95d54c4c7fd1baa9898ffb17552531ff56eaa4a63fe8dd5494d3febb56688a7fd769cd114ffaed29a229ff5da33444efd6baa918aefd76c4cab5dfaed39956bbf5da532ad77ebb46655e6fa73444abcdf4a6889579be8cd112ad77d9b4e255aefb36944ab5df66d189575df55510a2f3bd29a21458ff956c4a6b1ff2ad294d71fecd5109aef3eaa51535f67d10a2a6bfc74e1454d66febdd5492e3fd9aa21258ff956c4a2b1ff2ad294571fecd5108aebbeaaa2114d77ab544229cef4a68845379f554aa8a773d8995514ee7a532aa29ecfa22554539eeacd1119f3dd29a2233e7ba3344467dd7626558cfbae94cab19f75d1995633f6bd112ac67ee7a21458cfdcf4422919ff1e5545233c7fb35442479df66a5548e3fe55b1289c7fcab4a513c7fb35442279df66a5544f7db5522889fbb68845113fe6caa8a227fe54512344f5fd5551081f3f929a2103def5552aa07dde6265540fbbc94caa81fb7a8895503f77510a2a077f6aed3540f7ed5526a81f7d9894d503efb2529aa07ef6a213540ffacac26a81ff593549503f775108a207fce9551440ffcc9aa2881dfdabb44d03bfb2b689a07bf6aa91340fbecc4a2681f7d92944d03f7b51089a07ff44611340ffad2aa2681ff994544d03afdd76c4c455fbaed5988abf75da731157eebb46622e7dab344445cfb4e68888b9f68cd111157ed9b56222afdb369c4455fb66d1888bbb6c4cab11776d3995622eeda332ac45edba225588afd75da8b1177ad8951622f75d10a2c455fb66d3588bf96a2a6b1157ed9b45622bf5d768a4457eb56d1488bbd6c4a29117bae8845222fe5caa8a445df36263388bbe6acc671177cd198ce22f79d1119c45fd39563388bfc6a2c67117f8d148ce22afdb3689c45fe94511388aff55da071177e98940e22f7d51081c45fda9550388bfd4a2a07117fc93540e22ff522881c45ff244d0388b1fecd51089677d9a95512ffa22681a255fdaed89846bfb5dab308d7f6bb4e611afed7694c23cfd566888479fa9cd1108f3f529a2211afeb36ac4235fd66d38846bfacda5108f7758995611eeea732ac23ddd4a655847dbb444ab08dfb6bb51611ef6b12a2c23ded4a545847ddb4428b08d7f59b4d611fe6a8a9ac235fd66d25847beac4c6708f7d5598ce11efaa5319c23ef5a2233847fab2ac6708ff95458ce11afeb3691c237fcaed03847bf8c4a0708f7f12940e11f7e51081c23fdc95503847fd8a2a0708ffd13540e11efcb1311423df956622847bf29cc4508fbe68888a11feccab11423fe951622847fe319c4508ffe10388a118f7a9755273fc65153540ffc88a22681a80d32148b3b097c47de427eadefba9dcf42b3b5bbc5a989b20195c8e3fca3a657ce1a4cadbbe0ede400b2239029dd163e345f3291a2db00062ff5 else (if i<5 then 0x7ff64a11340ffec92a2681dfeebb56222efdb36ac445dfb4e55888bbf68cab1115feebb4e222efdb369c445dfb5653888bbf68ca71115feebb46222efdb368c445dfb5651888bbf69ca31117f6d3895622feda312ac45feb4e14588bfd68c28b115feebb4d622efdb369ac457fb62d3588bbf6c4a6b1177ed194d622f7dd109ac45fdb5613588bfe69c26b115feebb45622efdb368ac457fb62d1588bfd6a5a2b1177ed8945622efda728ac45efba211588bff28c22b117fad5845222ff5a708a445feb4d51488bfe6ac467117fcd188ce22ff9a2b19c457fbaed1388bbf6cda27115fed8b44e22bfdab689c45dfb6251388bbf6aca27117bee8844e22ffca3089c45fdb9551388bfd6a2a27117fe98b40e22ffd2b681c45ffa46d0388bff4ac207117fe91840e22ffd22a81c455ffaed9a44a7ff5db148967fd9b62912cffb34c52253ffaed5a44b3fecdab48967fd9a569129ffd769d2259ff66d3a44b3fecd2748957febb62512affb56c4a259ffaa98944b3fead3128967fd3a62512affd76aca255ff6ad5944b3ff552b28967fd8a56512cffa74aca255ffaed3944abfed5a728967feaa4e512cffb149ca259ff5693944b5ff555108973fd9aa2112d7fab544225aff4ea8844b9feacd108973fd39a21129ffb56ac2255ff66d5844b3fecd2b0894ffdab4e112affb369c225bdfaaa5544bbbecd4aa896f7d8a95512defa752aa25ddf6265544bbbe9ccaa897b7e8895512bf7d76a2a25befaa94544b7dec528a896fbd3a51512ef7b12a2a25eefa214544a7fed5a6a8957fd9b4d512fe7a8a9aa25bf7aaa3344bbeecd466896fdd8a8cd12dfbab519a25df76263344bbeeacc66897bde888cd12febcab19a25fe75163344affb5da268977f59b44d12dfed5489a25dfd6691344b7fac52268977f58944d12efeab289a25efda211344bfbb2aa26897fb54544d12bff57681a25bfe6ad0344b7fd55206896ff98a40d12dff2b481a25dfe6250344bdfd44206897f7a5540d12ff728a81a25ff64d50344affb5dab108f7f59b56211efea72ac423dfd4a558846ffb5da7108f7f59b4e211efeab29c423dfd4a538846ffb5da5108f7f59b4a211efeab294423dfd4e528847dfa9c25108ff753895611feea512ac23fed4e145847fda9428b08dff6bb4d611efeb369ac237fd62d35847bfac4a6b08f7f5294d611f7ed109ac23fdd56135847fea9c26b08dff6bb49611efeb3692c237fd62d25847bfac4a4b08f7f53949611f7ed1092c23ff94a125847fba9aa4b08ffd5588ce11ffaa5119c23ff549633846ffb5da4708f7f59b48e11bfeb1691c237fd56d23847bfac4a4708f7f55948e11f7ed1091c23ff94a123847fbb2aa4708ffb54548e11ffe31681c23ffc56d03847ff895a0708fff15840e11ffe25081c23ffc49503847ff2ac44508ffe53 else 0x5a2b19f7dd8945633efba528ac67ef7a21158cffea8c22b19ff5d2545633ff3ab08a467fe74a1148cffce92a2919cffebb62923cffb36c52479ff6698a48e7ff5dab491e7fd9b56923cffb34ad2479ff6691a48f3ff5531291e7fd5a62523cffd54aca479ff6295948f3ff5523291e7fd8a46523cffab48ca47affaaa8848f9fecd51091ebfd5aa2123e7fab344247cff4668848e7fed5ab091e7fd9a56123bfdd7694247dfb66d2848f7f75525091f7ed9a4a123dfdab494247dfb5652848fbf68ca5091e7fd9a46123f7da508c247bdfaaa5548fbbecd4aa91ef7d8a95523eefb132aa47ddf4665548fdbf444aa91ff6d2895523df7d54a2a47bef6294548fddf4428a91ffad2851523cffb348aa47befaa91448f7dec522891efbd5a45123f77d108a247feb4a11448ff9f2aa2891cffd8baa9139ffab7552273ff4aeaa44f3ff5533489cffebb62913cffb36c52279ff6698a44e7ff5dab489e7fd9b56913cffb34ad2279ff6692a44f3ff5531289e7fd5a62513cffd54aca279ff6295944f3ff5525289e7fd8a4a513cffab494a27affaaa8844f9fecd51089ebfd5aa2113e7fab344227cff4a68844e7fed5ab089e7fd9a561139ff956942279ff6692844f5fec525089dff6bb46113efeb368c227bfdaa91844fbfacd23089eff55a46113efeab28c227dfd4a51844fdfa9423089ef7eaa95513eefb352aa27bdf62a5544fbbec4caa89f77d2995513f6fd112aa27fdd4625544f7df5528a89efbd8a51513f77d10a2a27fed4614544f3fecd24a89ef7d5a49513ff6d548a227fed6291444ffdaad22889ffb52a45113ff6ab08a227fed4a11444ffda92a2889dfdebb48d13efbb3691a27bf7aa92344fbeecd24689f7dd8948d13efbab291a27ef7a212344ffe69424689ffd51848d13febcaa91a27fe75152344effd5db1481dffabb56903dff314ad2077feaed2a40effd5da3481eff92a46903f7f2b544207efe4aa8840fdfc8d51081dffabb56103bff356ac207bfeaa95840fbfc94ab081dffabb4a103bff35694207dfe66d2840f7fd5525081dffabb46103bff3568c207bfeaa91840fbfc94a3081fbf92846103fef3152aa07fde4aa5540ffbc8d4aa81ff792895503fef2312aa07fee4a14540ffdc8c28a81ffdabb4d503ffb3169aa07ff64ad3540ffec8da6a81ffd98a4d503ffb2549aa07ff64693540ffec9426a81ffd9184d503bff57692a077fe6ad2540effcc5a4a81effaaa49503eff31292a07efea212540fff49424a81dffabb45503bff3568aa077fe62d1540ffdca5a2a81ffd93b45503dff5548aa07dfe6251540fbfc94a2a81fbfa8845503ffe2308aa07fde4951540ffdcac22881ffb92845103ff724a8a207ff6aed1340ffecc5a2681ffd95b44d03ffb25689a07ff66291340ffecad22681ffd92a44d03ffb2b089a0))) else (if i<9 then (if i<7 then 0x5df7d548c28bdef4a518517dde94230a2cffd8baa9359ffa575526b3ff46eaa4d73ff553349acffebb62935cffb36c526b9ff6698a4d73fecd2549ae7fd9a46935cffd54c4a6b9ffaa9294d73fec52529ae7feaa46535cffb148ca6baffaaa884d79fecd5109af3fd29a2135e7fa334426b7dfaed584d7bbecdab09aef7eaa56135eefb34ac26bddf4a5584d7bbe8cab09adfdebb4e135efbb369c26bbf7aa9384d7beecd2709af7dd294e135efba329c26b3ff2ad284d73fecd2509afbdd384a135cffb348c26bfcfaa9454d7f9ec528a9aff3d2a51535fe7a34a2a6bfcf4a1454d7f9e8c28a9ad7febb669259ffd76c524b9ff66d8a4973fecd31492e7fd9a4e925cffb348d24b5ffaed89496bfed5b1292e7feaa62525affd769ca4b5ff6ad394973ff5527292e7fd8a4e525affd768ca4b5ff6ad194973ff5523292e7fd8a46525d7fd554424bcff66a884979fe9cd1092f3fd19a2125affb369c24b7fbaed28497bf6cda5092efeeaa4a125efdb349424bdfb4e528497bf68ca5092fbed384a125affb368c24b9ff66918497df69423092df7ebb4d525eefb369aa4bbdfaa935497bbecd26a92ef7d8a4d525eefb129aa4bddf46535497dbf4426a92ff5d384d525feda509aa4b3ff62eaa4567fe9dd548acffd2baa915affd76cd22b9ffaa99a4567ff5db148ae7fd9b62915cffb34c522b7efaed4a4577df552948aefbd8a52915cffb349d22bbef5293a4573fecd2548aefbd4a4a915affd76c4a2b5ff6ad894573ff553128af7bd4a62515affd769ca2b5ff6ad394573ff552728ae7fd8a4e515affd7694a2b5ff6ad294573ff552528ae7fd8a4a515ef7a9494a2baffaaa884579fecd5108afbbd4aa2115e7fa734422bcff4a688456bfecda708acffcab4a115affb369422b9ff66928456ffb5da308af7f59b46115dfed548c22bdfd66918457fdaa52308af7f53946115efea528c22befd4a118456fbf5da4a8af77d9b49515defd5492a2bddf66925457f9ea524a8af77d8949515eefa7292a2bedfa2125457fb69424a8aff751849515bf7d76ac229befaa958453bde94ab08a5fbebb4e114bf7d7694229def66d284537df552508a6fbd5a4a114f77a7094229fcf4e255453f9e944aa8a5fbebb4d514bf7b169aa29eefa2135453f9eac26a8a7f9d384d514bf7d7692a297ef62d254537df5524a8a77bd8949514f77d1092a29feb4a125453f9e9aa4a8a5fdebb56233efbb36ac467df74a5588cfbee8cab119dfdebb4a233efbb3694467df7565288cfbee8ca5119dfdebb46233efbb368c467df7565188cfbee94a3119fbdd2846233feba512ac67fd7462558cffce9428b19ff9d1851633bfbd7692c67df766d258cefeec5a4b19f7dd8949633efba3292c67ef7a21258cffe69424b19dfdebb45633efbb368ac677f762d158cffcea else (if i<8 then 0x695848fbfe8cab091ffed5b4a123ffda3694247ffb5692848fff68d25091dffebb46123bffb568c247dff66d1848f7ff5523091f7fd9a46123dffab48c247dff5651848ffdec528a91ffbd1851523bffd768aa477ff6ad1548fbfecda2a91dffd8b45523ff7a968aa47bffaa91548fbfecd22a91effd8a45523effb128aa47ffb4a11548fffa8c22a91ffbd8a45123ff7ab48a247fef5611448fbfead31289f7fd8a56513bffd76ac227dff66d5844f7ff552b089f7fd9a56113effa52ac2277ffaed2844f7fed5a5089fff51b4a113dffd5494227bff5692844fbfeaca5089ffbd8a51513ff7a50a2a277ffaed2544effec5a4a89effeaa49513effb3492a27bff6292544fbfec4a4a89ffed2849513ffea3092a27ff762d2344ffeeada4689ffdd5848d13fff256ac207ffe46d5840fffc952b081fff91a56103fff2b694207ffe46d2840fffcd5a3081fff95b46103fff2568c207ffe5691840fffc9523081fff9ab49503fff31692a07ffe46d2540fffcc524a81fff91a49503fff23092a07ffe62d1540fffc95a2a81fff92845503effab4c4a25dff6295944bbfec52728977fd5a4e512bffd76ac225dff66d5844b7ff552b08977fd9a56112dffa74ac225dff4e55844afff5da70896ffdab4e112effb369c225bffaa93844bbfecd270896ffd5a4e112effab29c225fef6294544bfde9c28a895ffebb4d512effb369aa257ff62d3544b7ff5526a8977fd9a4d512dffb149aa25dff6253544bfbeac26a897fdd384d512ffeab089a25ffe62d0344bffcada06897ff98a40d12fff2b481a25ffe5610344abff5db34ac67fd9a4e958cffb34952b19ff6691a562bff5da72ac57fdab4e558cffd549cab15ffaed29562bfed5a52ac67feaa4a558affd768cab15ff6ad195633ff55232ac67fd9a56938cffb34952719ff6691a4e33ff552b29c67feaa4a538cffd548ca713ff56eaa4a27fe9dd54944ffd1baa928affd76cd251df70ed9a4a33ff553349467fd9a56928cffb349d2519ff6691a4a2bff5dab29457fdab56528cffd54aca515ffaed394a2bfed5a729467feaa4e528affd768ca515ff6ad194a33ff55232945bfebb4e128e7fb369c251affaa9384a39fecd2709473fd594e128e7fa329c2515ffaed9a4633fecd2b48c67fd9a4e918cffb34952315ffaed59462bfed5ab28c67feaa56518affd769ca315ff6ad394633ff552728c57febb4a518affb5694a319ffaa929462dff5da508c73fd9b4a118d7fd5494231cff669284639feaca508c73fd394a118befd769c4abddf66d38957bbe94a712af77d194e255befd76944abddf66d28957bbe9ca512af77d194a255f6fa70944ab7dfaed18957bbecda312af77d3946255eefa528c4abedf4a118956fdf5da70a2dfbebb4a145ef7b369428bbefaa928517dde9c250a2dfbebb4614 else 0x69658594964c591164258f963a58d162e589961c58516105831608581160057e95f457c95ec57915de57615d657495d057295c456f15b656c95aa56915a2568159e55a152e53d94bc521144e50a94064f913c04e4136e4d293284c112e64b212aa4a3126c493122e48511e046a918c45c915a44d910643990b241f905e41010284038ff23f60fbe3ea0f883da0f483ca0f083ba0ec63ab8e9639f8e603908e0c3760dba3670d7e3598d5034b0d1233f0ce43340cbc32a0c8a31c0c5a30d0c0e2fe8bd62ed8b982de8b502ce8b1a2c10ade2ae0aa42a00a6c2908a2027f09d826d099625e095a24e891c23f08de23008a22200862212083220507fc1f707be1e9878c1dd87601d007201c006de1af06a41a3066e195863c189861017f05de17285ac1660578156053814584f213384ac1238470114843210503f40f583b80e683780d703420ca03120bd02de0af829e09f825e08f021a08081e407281b4067818805d0156050812404180e803180a4023806c01580380070001dff4a939563bfe8d272ac77fd1a4a558effa548cab1bff5692a4e2fff5da349c6ffd5a46938dffa548d271dff4a9594e3bfe8d2b29c77fd1a4a538effa548ca717ffaed5a4a37ff552b4946ffd5a4e928bffd768d251bffaa91a4a37fead234946ffd3a46928effd54aca51dff4e9594a3bfe8d2b29477fd5a4e528effa349ca51dffaa9194a3bfead2329477fd3a46528f7fab69c251eff46d384a3dfead270947bfd1a4e128effa74aca31dff4a959463bfead2728c77fd2a4e518f7fd7694231eff56d28463dfe9da508c7fbd2b4e145ff7a369c28bfefaed28517fde9da50a2ffbd1b4a145ff7a768c28bfef4ad18517bfe8d2529af7fd2a46535ffba569c26bff746d384d6fff5da509aeffdab4a135fefab69426bbffaa9284d7bfe8ca509adffebb46135dffd548c26bdff669184d7bfe94a309afbfd2846135effb149ca4bdff46939497bfec523292f7fd3a46525bffd769c24bbff6ad38497bfecda7092effeaa4e125effb349c24bdff46538497ff75da5092ffed3b4a125ffda369424b7ffaed18497bfecda3092effeaa46125effb348c24bdff4e518497fbe8c26a92f7fd8a4e515effa549ca2b7ffaed384577fed5a708af7fd9b4e115dffd549c22bdff66938457fdea52708af7fd294e115bffd769422bbff6ad28457bfecda508aeffeaa4a115effb349422bfef52928457bfe9ca508afbfd384a115fefa7092a2bfef4ad58453fde95a708a7fbebb4a114ff7ab694229fef4ed28453fde95a6a8a7fbd284d514ff7b1692a29fef4ed25453fde9c24a8a6ffd5b62923dffa36c52477ffaed5a48f7fec52b491effd8a46923dffab48d247dff5698948fbfec52b291f7fd8a46523effab48ca477ffaed5848effed5ab091f7fd9b56123dffd54ac247dff6)) else (if i<10 then 0x493c44edb3adce8139fce633984e433894e073734dab3614d6334b4d07333cc9b31dcc3f3024be52eacba92e34b8b2db4b4f2cc4b2b2ca4b232c74b172c4cb0d2c1cb032bf4af72bbcae52b84ab72a3ca6d29a4a53289ca2327fc9e926bc97524ec90d23648bd2264873212c8151f7c7ab1dd47431cf473b1cc472b1ca470f1c346f11b446b31ac46991a5c67b196c63d180c5d316dc5891574539144c4f113244a311a443510643f50f3c3ab0dd434f0c542e10af4285095421f07ec1c3064c18d061c17f05dc149051c12b04a410d03bc0d102dc087015c03f00f401f0073ffcff7bfbcfe73f98fdebf58fc83ee8fac3e78f92be16f7ebdd8f73bd9ef5fbd58f4dbd14f3d3cbcf25bc60f103c0aef9bbb0ee03b48ec93aeeeafba9eea5ba94ea3ba88ea13a54e8839eee6fb9bce68b9a0e61b96ee54392ce43390ae3c38eee34b8bae25b878e1d3854e0d3806e0137deded378cddab766dd0372adc9371edbd36cedb236b4da8b676d94b64ed8ab624d83b5f8d7cb5f0d7ab5e4d77b5dcd75b5d0d72b5c4d6f35b2d6bb5aad69359ed663592d633584d5eb572d5b3568d58355ed55b550d533548d513540d4f3538d4cb52cd3eb4ded2eb484d1a3444d0833ecceeb386cd5b322cbcb2c2caf32bacacb2acca9b274c913242c8ab228c8331f0c74b1b4c61b16ec5a3166c58315ac553152c53b124c4030fac3930b4c22b066c10b03cc09b020bf9afacbdcaf44bc3aef0bb2ae96b9dae50b8b2df6b71ad90b582d2ab3eaccab312cc2b2f2cb6b2c2c7eb13ac14af92bc8af1abaaaea2b8aadb2b4cacaab0eac22b06abfaaf6abc2aeeabaaac0aa72a96aa02a52a8caa06a77a9bca65a970a522922a482906a4128e6a31a8a8a292886a1a2864a14a8249fe27e29ed27889dca76a9d9275c9cd271a9c626f29b1a6ac9a2a684996a64098f2618981a60097ea5f297aa5e496ea590959254094824f6935a4b69252468911241a90023de8f6a3b68ec239e8dca35c8cea3128bca2ec8b1229c8a5228089b2240885a1ec870219e85d215284d211483da0d482a208481fa07c81da07081aa068818a05c815a050812204080fa03a80d202e80a2026808201a8052012803a00a800a0007fe1ff27fb9fe87f99fe27f79fd87f49fce7f21fc47ef9fbc7ed1fae7e91f9e7e71f987e59f907e29f827de9f767dc1f687cd1f007b99ec47a41e747949e1e7809dde7699d807521d167391cac7219c507081bee6ee1b946d79b2e6bf9af86bd9aee6ba1ae26b71aac69e9a4868619e867899e067619d267319c667119c26651970652992464818ee62f98986249890622188061e987461c186c61a1866613984c60b98105fc17d25f397ca5ed97b45e697725d4172e5c217045c016d45ac96ac5aa96a45a796985a596905a296845a0167a59d167059b966c599966059 else (if i<11 then 0xd02cd49a00229260129160043e230982e7d348a4340b4f000ea7f00948b0021f11924260b9a4521a05a788c2d009600475348a4347f4d000c26a00948b0021f11924260b9f4521a05a780e012c0088c9a308a4340b3501544961489c3418419a0da072d11d3231529f92e0777ad932961489c34182d11d4a414b81ddeb64ca5852270d061065a0f21e03b8760ea1d0398720e01bc3706d0d61a8348680ce198328640c6188308600be1782e85c4b616c2d0594b01602b8560aa150298520a21402784e09a1302584a09212223a4728e5192294508b1112214448650d21142084904a0841880900a004027e0fc1f23d27a0f41e03b0748e49c8390700dc9b03606a0d0198320620c01782e05a4b01602b0550a5149292502a01442744e49e1312614c0981282404608a10a21840880900a004107d0f91f03f0790f21d13a0740e01b0340640b89602c0544a014a26c4d0991302784a89412e2384688c1162284488811e2184288310e1fa3f07d8fa1f23e07b8f61ea3d0798f21e23c07f0ec1d43a0730e21dc3746e0db1b43646c0d71ac3546a0d31a4344680de198328640c619c2f45e0bb1742e45c0b716c2d45a0b31642c4580be1582a8530ae13a2704d89a1322604b89612a250498921222404f08c114220430841042383e87c0f61e83c8780ee1d83a8740e61c8388700fc1b0350680cc190310600dc1582f84e09a12c2504708c114220430841042004e06c0fc1702d0560a81382604a090118220420801701c0340600b0140240400f80d01601c04809bded17b1debd7acdea97a75e8d79fde7179a5e5f7955e4d78f5e2f7885e11780ddf5779dddd7755dcb7705db776b5da3766dd937615d7975b5d617555d4974f5d31749dd1f7465d11741dd0173edcf373b5ce37365cd17315cb572adca37255c8b7205c717185c4b7115c3970b5c21704dc056fedbeb6f85bd16f15bb96ec5ba76e6db876dedb676d65b4f6d15b3b6cbdb256c75b0f6c1daff6bd5aeb6b7dad36b15ab96ab5aa36a75a996a55a8f6a15a7f69e5a7169a5a636965a51691da3d68b5a1f684da0567ed9f367ad9e167559cb670d9b766bd9a5666598d65fd97765b5963654d94564d5923645d91164258fb63c58e963758d563258c162d58ab62958a1626d893623588361e586b6185855613584160c5827607d8115ffd7f55fb57e55f6d7cf5efd7af5e757875e057775dbd7635d757555d357435cdd72b5c7d7135c256ff5bbd6e15b5d6cd5b0d6b55a9569d5a4d68959ed671599d65d594d64758fd63358ad61f585560957fd5f757ad5e3575d5cd57255c356dd5af568d595562d57f55cd56d559d561555d54b550d53b54dd503537d4bd526d465510540b4f4d3ad4dd533d4c5d2e14af529949cd23f482d1d7467d16944c50f9437d0ab420d05d40d4fff3f64fa33db4f else 0x6595b994521a362689059430741ca32e80806290d20416b722a6800f4028ac0459519a48a3c148696e094e0ac04032ca8cd2290d1fd6e454e164c234518bc0403498a434b722a60009317808b2691e0a434454e000fe2f01164d23c148688a9c2e930b221091d470013600926290d2dc169a2e9b098594508424b71c00404290d1fc169a2e9b098594508424b73a80404290d02c869a002292601329b004542c8982e7d200a4340b4f000ea7f00994d8022a16524260b900521a05a785a01329b004595b9d4521a3fa685a01329b004595b8e0521a21a689059430741ca33880806290d02cd8454d01468980100cb2b7328a4346c4d0000a2f15808b29c328a4340b781b0b25d7800806931486816b736001260901165386514868166c0002404594e194521a059b056a503815e0020196530b7328a4347f360ad30020196538290d1fc162b5281c0af00100cb2985b994521a3610c56980100cb29c148681643422503e1039a90be01018a4340b5c1648c9a37a05101f08290be01018a4340b5c1648c9a213c1df0a5a48138961489c34184182cb255000c88c1d071c4ba4a0100d28290d28c16b74e0006446430741c5d7f9294602018a4348105add3800191190c1d071c546f725280040314868166c4e0006446430741c712e80806290d28c16b72c2710c941b118421230938020214868fe0b4d21928362308424752700404290d02cd49a432506c4610848ea6100808521a0595d3432230741c5d5192804034a0a4348105add3432230741c715192804034a0a4340b3626864460e838e25d0100d28290d28c16b72c268e2811b1184212309380202498a4340b4d1c502362322842122700404290d02cd49a38a046c4645084246100808521a0595d34004524c0279408087c461305cd25614868169e001180a2b01204f269518a434095ba70e261519185e0201a4c521a40add307130a8c8c2f0100c521a40adcae980024c8c2f011e4d2290d2053832232183a0e51928040314869020b362680a714c00806655b8a4346c4d0c88c860e839465d0100c521a4082d6e584d1746c4610848ea4e009b00493148696e0b4d174d8362322842125b938020214868fe0b4d1746c46450842475009b004290d2dc16574d001149300994d8021f1184c173e958521a05a7800753f804ca6c010f88c921305cac290d02d3c4616804ca6c011d56e290d1fd3432232183a0e519c4040314868166c2c2680005178ac04464e194521a7802cd85d780080646498a434b7059b0baf00100c8c290d2dc166c2b801260901119386514868166c0002404464e194521a059b056a503815e0020191930655b8a4347f360ac8c980100d38290d1fc164a2c0d88c21091d4c2010124c521a05a6894581b119142109184020214868fe0b4d128b0362322842123a80404290)))) else (if i<18 then (if i<15 then (if i<13 then 0x38a04be8a108487001011b4521a5c02cae9a38a04be6d4508424b82700404290d02c869a0022926013ca040467368982e56200a4340b4f001262f0119cda795c8a434814e001262f0119cdab91e0a434454e000fe2f0119cdab91e0a434454e211281f081cd48360080c521a059b4b29a37a05101f082906c01018a4340b3696534840d830de046e920642a47a5052270d06106b6059a0066d899687e464e0c5081b06374de04240c854961489c341841ad8d0033694cb00b1f9193831422503e1039a909801018a4340b36919346f40a203e1052130020314868166d2326800030225c76334f8e8ceb914868886d4e0000693040e936675c8a4346d4e00006081d26cceb914868da9c038d94ac019c2084b64b0a44e1a0c20ca6584d0c40006180b002944e99c521a05bc4da942f80406f11486816b83695c0006180b0029d338a4340b789b4be0101bc526290d02d706d2f80406f11486816b83695c0093008293a6714868166d0000d262e5302410f24d99d72290d204da00018a9cc97321713a290d1ad020b0000c5c634da74521a4082ddee62d9ad4a2e883bd16931489c34183d2056c0b2d11dcc5b35a945d0a77a5852270d060f4815b02c9e572380006931726d3a290d204165c77b3e427e35bca209d45a4c52270d060165a239f9f6ef90bc6149d4b0a44e1a0c02ca6582380006931729812087926cceb914868da450000cfe2e5302410f24d99d72290d1b48b23518b12f351729812ef5b26d2c291386830763f9688a3d0000c54dd4b9913a290d02c8a2a4bb613a96930a44e1a0c1d8fe0b2d1147a00018b8c69b4e8a434ef05915ba5b35a945d1077a2d26291386830835b02cb4451eb74b66b528ba14ef4b0a44e1a0c20d6c0b2795c8a3d0000d262e4da74521a05916045c77c80826b794413a8b498a44e1a0c20c165a0000cfe2e4da74521a05915462c52c7c5c979401ddeb64ca5852270d060ec7f2d1147a00241643a0e38974680201a50521a5182d6e9c00120b2860e838baff1a28c040314869020b5ba7000482ca183a0e38a8dee345000806290d02cd89c00120b2860e839e8712ea8c04031486816b722a710c94261644212308e0020214868fe0b4d219284c2c88424751c00404290d02cd49a43250985910848ea6100808521a0590d34482c8741c5d518d004034a0a4348105add34482c8741c71518d004034a0a4340b3626890590e838e2a32e80806941486816b722a68e281261644212308e00202498a4340b4d1c5024c2ca2842121c00404290d02cd49a38a04985945084246100808521a0590d34004524c027940808a8591305cd24014868169e00015fe2b0116546813c9a4521a04add385938985462f0100d26290d2056e980024c5e022c9e4d2290d20538482ca183a0e518d0040314869020b362680a714c008 else (if i<14 then 0xd385e011c804a34c00842290128d301e0128df2711200946f71200938243900896025ba696e9a5ba6844a34c00804a34c00946980f00946bc0128d78024e178049c16a600407058080e0b013c00e0b0102404b72f024042204809349a4d1c8de1b06010b6488cb64642a48a5452270d060ec7f0182cdcb62d11d3a3125920360c37810b7196b0c854914a8a44e1a0c20e62a20182cdcb62795c8e9d188d4641b061bc085b8cb4c902a48a5452270d06107310182cdcb62d0e4869d18a1c360c37810b6488ab6c642a45a4c52270d06107295100cdcb62a96416474e8c4e4840d830085b24455b2321525a52291386830763f80cdcb62a96416474e8c46a840d8322ad337810b6321525852270d06106035b1b8aa59058e4869d1880108950e838ba4a7f8d14602018a4348105add3800422543a0e38a8c94f71a280040314868166c4e00108950e838e25d1a00806290d28c16b72c27000844a8741c712ebd094a30100c521a05adc8a9c078654ea809a4122263e9a4ac3e01a5452274182cdc5a1f9193c31001bd041d0717494340100d28290d28c16b74e000de82430741ca3253dc68a00100c521a059b1380037a090c1d071746802018a434a305adcb09c001bd04860e838baf42528c04031486816b722a710c9439a084212270e0020214868166a4d21928734108424611c00404290d02cae9a43250e68210848c24e00808521a0590d346f410741c4a518d004034a0a4340b36268de820e838ba340100d28290d28c16b72c268de820e838baa32500806941486816b722a680006800b00294411ecd2a41486814b84ea50e6610080d48301486904b82ba65081b06010b648730c8548f4a0a44e1a0c1f104b60182cd06d2d11d38314206c18042d921cc321525a362913868307c412d806683694cb00b23a7062844a07c204c520d8020314869040b36a6800030225cf09f3b99d72290d1b5380001a4c10774d99d72290d1b538ca38024eea6404496c8b498a44e1a0c1688e9c1887850aa112ad24173d9a4a8404b1f0341801a08166e2a9648e9e18a11281f0817d48360080c521a4102d70594d210360c51010b6df240c8548f4a0a44e1a0c1f10403059b8b43f2327062840d83144046f96c90321525852270d060f882019b8b053058fc8c9c18a11281f0817d484c0080c521a4102d70464d001ea06160052869521187c290d2e0149d16004069434a90521a3fae08c9d4a1846c0101a9060290d2e0ae464c801020616004d2a4230f8521a5c0293a611b0040681520c126290d2e08c99308d8020340a9060290d2e0ae464c8012601408c0d23e148688c9d43250be6d108489cb81c00404290d1fc169a43250be21091d47001011b4521a5c02cae9a43250be6d10848eab82700404290d02c869a38a04be21091387001011b526290d2e0169a else 0xc1488c34143c994b2501d4748d2869a8a59194a214401105818c02c9888c341438994b2501d0a4fe464e4a145134a2144011989d016064e0b052230d050f25d2c94074b7231a800fe69a8946ff430741c5d2c9208c328ea444a16409e0160a340c0521a5ba710c1d0728cbab469a584e18409e8166e188a434b74e00162a27f2244011409c016065a1806e9c1623852230d0523a652c9408c3a69a8a5efe10045027005818c09c1624d0c2911850ca5928118741a94289fd134488022813802c0c9c162dd1c2911868286a2e964a0461d001ecd3512183a0e7b9c5465924118651d488942c7c05828c83014868d89c430741ca338ad12c270c34d060b330c4521a3627000b1513d9122008ad0e80b031b0b8374e0b11c2911868291d3c964a0461d34d452f7b080227405818b89c1624d0c2911850f25928118741a3634d452c7b224401105818d85c16238461a0a1fce2592811874294e291320100a91322000a913201522cc02a45980544d34b8701a0b02480b82a4f2511c29130682e7934964a83e4091944b10e839465d2c9208c328ea511a250b204f00b051a060290d2dd34a266251081f08204dea42fc9c481505824cc5928918762f14a6834b85134d2e1c06c80e00b020a93c94470a44c1a0b9f4ca592a0f88c6c512c43a0e519c4b248230ca3a94468942c7c05828c83014868d89a5226402015226422015226402a45980548b300a7400005130d2e89100682281382d0c037161e45e468e8a4d2594e4a144c34b880228138180587917919262934964349c942892e89100682281380b0f22f232dc52612ca70d4713096544a3234752689128590278340c0521a5ba60002f5134d2f20428701a0b020a93d31490a44c1a0b9e4ca592a0f902463628962a3430741c5924118651d488942c813c02c1464180a4346c4d01548716d39e5099488942c64182dcca5914868d89a522640201522642201522644001522cc02a459805729d5ca745a010022842125b9d498296982c34594d0011421092dcea6c2e94452d3058c434594d17016d349a2852260b9f4ca540d164d89e6eac442123a974985114a4c161a5b964d89a6eac56e8a10848d85d26144520b0d165340028800a275169456e2932868b26c4d001122910068227403348b2f06c02c8c006e2712e891488034115a1d00c6c2e0dc12599402c8cd26e2712e2910044e8062e02526590d02cd846693713897448803411031b0b8092c8a4fe0b231754859693be5093448942c7c05190521a5b82cd846000240009520ad4aef03815e1284c25d22250b1d0c8b72c8a4347f3611856e76c3bd389b488942c74050a4347f059648ca34c00804a36700946ce0128d30020128d8e0251b1c04a34c008c20251bfc04a37b80896024d269302f0128c5e0251a60040251a6004a3012dd465d012d)) else (if i<16 then 0xe45c9d8849852930d02d025773b61de991488826720393c5c9d8824c340b4090c00d26e2752e87720a43c1a0792c0a6d2e3ec6a0a2c20416870f0681e051a8a5a4584082de2d8693713a970f0681e052e0d414932c0a5026d0580048a32f961a4ef438903415049907a9314a04da0b5c000480a3942c340a498a5026d05801a4dc51b813a97438a43c1a078d40a6d2e12c15224082c8a8714878340f0292da48105915a4dc4ea5c521e07814da5c25829261a4082c8a2c52c89e2ef4ca584e186a9b4d05a0381970290d2048a2c78a752c270c354b40b91480521a40c848a004dae5c05f693bd0e240aa8d7009911b4c853498a4348105915c05f693bd1e240aa8d7009911b4c84b14869025705914009b5c828e4294ec80da0a49869020b1a8693b2136828ae29059166aa377a6d2e22099809e351729812087924d72290d1fcda4577a8d36971104cec601a8b972a604821e4932b8a4346d22a8dde9b4ba2c441a099806a2e5302410f25c95c527f369146a2c5b265162911068267603b789e5c32275b1108f82c8b0a1627532291104cec0727a2c34d8499ac1645850b1328b1104c0e4f4ea5852270d060ecd82d440fe0b22c2858994588834133b01d3a296c13e212805914ae291104cec07278d45c1a6c24dde0b22c2916220d04c0e4f1a8b9b029881fdde0b22c2916220d04cec071a8b9b029883bc16452bb79b0ef4ea6444130393c6a2e14a4c347f05915dcde6c3bd6d1e4ea6444133b01c6a2e8549852930d02c8a576f361de9d4ca2c441a0981c6a2e850a4fe0b2295d46980100946ce0128d9c0251a60040251b1c04a363809469801048340251bfc2a0251bdc2a024d268269817808262f0128d30020128d3002518096ea37a009385e011c804a34c014040251a601e0216a6804a30128dee024e1c8042f012605e024c0bc04b74d2dd34134d2dd46980100946980780946980128e265d012dd46ff01270bc024e0b530020382c040705809e00705809e0090104c12024c2dc12020025d30860e83a54712ebccb315519192c270c34d066e058c4521a5ba7000a24b871532006c84e00b02170549e4a23852260d05cfa692c9507c4610848ea611489c30833702c621a69a510c21091d4c22912054f40b04999342f0d34c00a24ba1559200e03416042e0a93d31490a44c1a0b9e4d2592a0f902464508424614b09c3418699b8163114a69142109204e261478902a0b049985e290d34d34005144d2e850e036287005810549e490a44c1a0b9f4ca592a0fa50463622842125b9d52c291386830d34182c628a108496e75361751e29120682ad33d02c129a1780232d35128c3a0e38974b248230ca3a94468942d313e02c1468180a434b74e0741c715197568944789c30d34182cdc31148696e9c002c545194a21440113a02c0cb4300dd382 else (if i<17 then 0x4e3699016d30d41d348569a511c291305cea672b068ff2936a79d0dd4a21852210917d704e36990167f0d269d0dd4a2185221091d4be6405ca434b82b9b534338641e52291305cfa6727068ae6d4f291320100a91321100a90be015c29002b84e98002005125d12200d04502701bc7c9a2c3c8bc8c2933ae5386d5125c4011409c09a2c3c8bc8c931499d721a4e1b4002f4d980f22f40a4c52675c868da9c5138948880f841026f2c1211e240d0541609320ec5e293691934496ca484c1a0b99cb0521f4c65229231b53c6002a8d308b1488826761d8cdbc4f1682474675c86a106d4e0153022099d89e2d048e916296a16926675c86a106d4e015308b1104c9e2d048e9a82933ae4350836a700a984588826d43b0b4123a1493d72672b868886d4e4d546d46f26044133013c5a081d24cceb914868da9c6a37946b94c0882676300b4103a8424cce290d15cda9c51b51bc984588826601682075085c99c521a2b9b538004508424b63a8d88c1a14c1a1e0b2c0011421092d8ea4a230ec349a14c3e0e0b2c2e9ba21091d494361d869342949ad816462c2e9bab645084244a1b118761a4d0a41658000ecb90687ca53c8a130682e7d1f0a5260b23170670f83a2852260b9f4a41a499613c0b000ecea2d230ec34b614a68b00043b213a290f0681f0d3928c0b1936c2897051aa51a40b7936000724ec410e290f0681ea302b08db0a25c146ad24082de4d83901c521a04a4da48105bbdb00025af93b10438a43c1a07c34e4a302c54db051ab48b00b7936000354ec410e290f0681f0d3928c0aae36c2896d26c02de4451a81c340914b48aed87782c8a070082de2070082c0e0105bc400dc4ea5ce4290f0681e053697096cf1a829288105cd4521e0d03c0a4b1aa51a48105bc5b0005197d2935693bc481504990ae4b1e8a434813682d7000693713a97258a43c1a079c80aee36972303505250b00b930a43c1a079c80ad21aa50b00b78b60bea17789c30833411c530c0d492160b5c1b63c005c99000d26e2752e3514879d41a079c80a6d2e408960a4a02c8a290f03ce4052586928d278b60164500055465f4a349de2912054f4093212cae1a5c02cda451ac30520a2b868166d2281c020b0380416070082de2b830004141300829dea34da5c441339180722e532e412087924cae290d204daa377a6d2e291104ce460278b94c09043c926b90d204da43390b16c99458a4441a09990b80727b9c729d6c441020b8548c5899148882607278e53a8b0d361266b4082e15351626516220d04c0e394e8a49ed88820416571626516220981c9e9d4b0a44e1a0c360b43988204170a218a444133901c9e3917275b01a49a04170a77a2c441a099c80e391727452d888204ae0b77a2c5222099c80e4f1727434d88820614ef0590ddce76c3bd6d244c8882672038 else 0x88002a45e80548bd00c8544d64b8701a0b02480662a4f2511c29130682e7933964a840409b544cc4a2103e10409bd4836938902a0b04990b2511e8bc529a0d1b40021091d4be3805869ac295c418da004a21842123aae0706405869ac6d14c190ad64f2511c260d05cea67200a4fe6d762e9288610848beb81c190161a3f9b452ec5d2510c21092e0ea5f3202c346d1490d44e84a2103e10521cc8a32148902a7a05824c85117965341a36c320c9e1305cfa671e0a4344536a91320100a913201522f402a45e8053a60008014497448803411409c09abf1b8b0f22f5c8a4ce594e1b54497100682281380dc587917ae5262933965386d000bd36603c8bd721a40a4cce294e1b544df522203e10409bc8a329123c481505824da64288bc521a2ca6800a24ba24522008afce84d228cc583c17ae434672c9b538a24b8a440113a114662c1e0bd72930d19cb26d4e2892e89100448a33160f05e7f5c868ce59149b5380017a6cc03c17ae5261a338a48a6d4e0005e9b43a89b6970e034e00b02171bc49198a93c93450a44c1a0b9f4cf142b0fa3e46369c944d94ba14380d05810b8de248cc549e8fa4852260d05cea678a1587c7f231b496a26b25d0a1c06b78e00b02124662a4f24852260d05cfa672b9387c278f9b48c004ba611622099d816071bb789e4616a711c291186828795c94800a24b871532006c84e00b02124549e4a23852260d05cfa67949587c463688424755c13852270c20da65a058c5b61a4a21842123aae09c2912054f40b04b4ca69a17c1c3400514812e850e0341604248a93d31490a44c1a0b9e4cf292b0f9024636a2842125c1392c2913868305a058c5a6d94d2284212409c5704e478a4481a0a82c125317b4e0e9a4508424b83a960948f148903415699e816094d0bc00a28cb4d288510044e80b030de3e4d4e0b052230d050f263290e9724636a8a3285100441606268b052230d050e2635c94874943fcc48c6d4e00144fe69a244011409c016061bc7c9a9c1623852230d050da635c9488c3a513fa602008a04e00b03135382c49a1852230a1b4c6b929118741a0028a2ad34488023143a02c0c372c125382c470a4461a0a1e4c63a5c918daa28a88023293a02c0c494e0b126861488c2879318e8b01a5c918daa28aa24401105818922c5ca3852230d050e2631d4a4fe58231b538a44c80402a44c805490000a9002b85134d2e1c0682c0920248a93c94470a44c1a0b9e4cf292b0f9024636a8998944207c208137a9099271205416093214c8c3b178a5341a36a5d581c06c84e0a26f02c08492e0cc5494470a44c1a0b9f4ce521f47c8c6d4f16144ec4a2103e10521ccb048928902a7a05824c83b4d0bc52460d1b492db4f0a44c173e99cb0521f0688c6d000a442123a97d704e3682c62d30d41d34004a2185221091d570))) else (if i<21 then (if i<19 then 0x609330ed342f1491834825c0004212399849c821482d28d30d41d340043084246127208f0294a34c35074d0b50478478a5a85a4a1a435084d3a1a6df43084247327208f0294a1a8349a7434e2cdf430842473309e05294844a434822ba6866e18741e1129148982e7b3493834822ba78008a10848c2362306816d983444529a0022842123096094461d869b311838a5342d230ed2c1a6d1a4b112840a534e26cc69be2109184b04a1b0ec351298a4c52464d389b2df450842458250d88c3b0d1a8529a000ece0ed834462531450983417348f9262923278e03388c1e1129450982e6929069265814a7800a260a5ce4290f03cbccf25918662b1f0c102940d1a64f354e8006c9430c9d44a412054cc5725918762f408a434b84c80144972f0a43c0f393249646198ac7c304a068cab93627400a260a5c96290f03ce45e230cc563e1825034692c2746c615109c3083370fc1431520a48c1a832e13200510b144a44d8902a72330ec5e943496052460d1fd709d258a48c3e182e0c2580d1a93a99008c14801180014497438a43c0f2f48c9646198ac7c3040868cab9362766aa24b8a43c0f25918662b1f0c102930d195726c4e80136302f0f8601a32ae5262936274e4291f0c1021a5b24d3a00513052e87720a43c0f25becbc46198ac7c3040868d2584ea8982970f03cbc46198ac7c3040a4c34692c0a53a00120d8c258512910e240d054cc3b17a052629232e13200120c0e5061f0c102930d1a452464e92c8c3e182e034612c0a4d49d51a60040251b3804a36700946980100946ff0128de80251a6004120d00946ff0a80947011a0540435012e134b84d04d462f0104c5e0251a6004211480946980f00946f93889004a37a09004b94e090e40251a600a020128d300f010b534025180946024e2e4e4021a8085e02518bc04221780800a28ba5c380d3802c0918198a93c94470a44c1a0b9f4ce592a100da21091d570381489c341841b588e0b18a510c21091d570381489034153d02c12d61ea685e005125d0aac908701a0b02480662a4f4c52429130682e7933964a840409b51421092e07096138683047058c5ac2945084248138ae0708f120682a0b048f5342f6b0a51421092e0ea451a23c52240d055ac7a05825342f0028a3294428802274058189abf1ba70582911868287931964a03c5c9b5451996a1440110581a62374e0b0461a0a1c4c659280f128293fae4da00513f9122008a04e00b031357e374e0b11c2911868286d31964a0b91e289fd17100450270058186e9c1624d0c2911868286d31964a0b91e00144f34488022bf3a02c0c4d228cd382c470a4461a0a2e4f26d31964a0a279c5c40113a02c0c4519a705893430a4461a0a2e4f26d31964a0a279cb512200882c0c4519a7058b94708c34143f9c4da632c94052a44c80402a44c else (if i<20 then 0x53b1ace24a218421239984f0824d068524324c3a169e1305cf661200a4348235289c41d07208dea32e964908d128682c0b051a076304a0a56e454d289d0944207c20a42f914642912054f00b04998a22f2ca6834825c43a0c9e1305cf6691e0a434822280114210d04898b71c165b20b3642622294d00114210d048bab71c144b20b36366230b14a68b80b6ca284c1a0b994b2542024c526c4f399c4210d048ba4c1c144b33105a4c52b736269cce25ba28421a0917498512c90c166c14a6800513838e13114509834172a10016932c8a53ced739c0931198c2d14260d05cca40498a4d89e43a89b6970e034e00b02171c249198a93c93450a44c1a0b9ecd2561f2088d222f289ae97428701a5c05811c249198a93c921489834173d98644561f2088c6a25a89ac97428701a4905811c25c198a93c921489834173d9a4ae4e1f20a44460025d3111430741cf3411760e4a7f1194696138616e6e2d02c62d314869b29c0025d308b1104c6e0b03989c24f230b5388e1488c341432b4ca4005125c38a99003416042e124549e4a23852260d05cf669949587c82230842461270a44e183734cb40b18a683494430842461270a4481505824ccd3298bd341a0001182c34e000080902a89a898458a4441a098dcc4e1279185a2f891a611224e0240a981104cc4d4278b45e9334c20521a4e2284212361756e4e478a4481a0a82c125317b4db29a038145a98478902a53179956ed414869b46c4d228421230960948f120682a0b04b4ccc2f14a680e0516a611e240ab50cc2f891a4b0290d268011969a8c3a0e411bcba4a230ca448d12859440b052dcd05518250521a98a703a0e2ea8c948f1386016b73734cb4314a0a434d94e001bea269c652885100446e0b031809a9c160a4461a0a1dcca521d2088d225137ccaa34789c306e2d0c528290d4496e98003d9a6a2430741c8237a8dee4a230ca449112858160a36190aa301486938860e839464a4b09c300b36198b431698a434d94e001bea269bd91220088dc1606361709a9c1623852230d0510477911488c3a69a8a66f6100441606361709a2c49a1852230a208ee52230e9381a00455a6a3430741c82379748c32912444a165102c14b734144612914868b09c430741ca32ea584e1805adcdc5318b4c521a2c27000df5134e2a89100446e0b03180b0494e0b11c29118682877328e904469134d451510044160630160922c94a4d0c2911850ee651d270348223289bea332a584e183714c630814868b0b74c2913206008045a014d291f00100a9144df0e839046f519288c32912344a1605828d8642a8c128290d2692e1c06a89c20b02170923315279288e1489834173d9a4a43e411608d186f8741c6f2e8ca448d1285944a305828d05118250521a411608cb74d289d8944207c20a42f96090240a9e01 else 0x12200898016062c12646374e0b11c29118682877318f104b936cd545158d880220b0316093291ba705893430a4461a0a1dcc63c412e4da00513cdae8910044c00b0348c9a4519a70588e1488c3414411dcda635c94a6aa279c6c4011058189a4519a705893430a4461a0a208ee6d31ae4a4a44c80402a48d97c02b8523d4020010848be4e5c0e0da0b6c86928294d0010c210913970383699016d90d250529a663990c210917c70640595c349414ae0da9a663990c210917d704e36990161a4a0a5340010848e64e5b0e104290d2501709002184212272d870823c0a5341a4a02e12c5732184212398e0f0294d06928820595d6cc573218421239ad89c823c0a5341a4a02d2e1c5483544e705810b88524c80662a4a23852260d05cf667291010458919b53ca276251081f0816090a41b49448153c02c12641ea685e290d208db0e84cc53c291305cf6522006816822c289d0944207c20a426114642912054f00b04990a62f4d069046d300154698458883413381e09ee71c8b4127733ae6242936a700a981104c9eda1c8b412770d24cceb9400a4da9c02a611622098e45a093ba5834da5c99caf12149b538054c22c4413278b412770d368ceb9890a4da9c6d39d46b94c08826601c8b410778919cae9314868da9c51b69ce981104cc04f16820ef1233ae526290d1b538004ba622286578741d1541175fca32cc18689613868306e2382c62d614addb29c002892eac908701a0b02172403315279288e1489834173d9a4b254202084212308e04e1a0c1b9ac47058c452d94a2184212308e0481a0a82c12666b0f5342f14b651421091b0bab71c23c481a0a82c123d4d0bdac296ca28421230914688f120682a0b04b58cc2f14b6534008cb59441d0728d046f2e964903446894341605828d03f1825052b798a703a0e2ea8c688f13868300b373588e314a0a56ed94e001c4a26b465288572880224d05818c0fc1ba7059311488c34143b994b2501e20800f66b2890c1d07208dea32c921ee3448894341605828c83f180a4d89c430741ca31a2584e1a0c02ccc4718b58526c6ca7000e251359ec8972880224d05818d85c7e0dd382c470a4461a0a208ee59280f1aca29a3d8401105818b8374e0b126861186828823b964a03c149b000f36b28946f4430741c8237974b24848894341605828d03b180a56e454e2183a0e519752c270d060166e1e8c5ac295b915380071289acf344b9440112682c0cfc30114669c1623852230d051047732964a0d6514d1e6200882c0c60228cd382c49a18461a0a208ee652c94052a44c804420114a91f00112a91ea0112a89c41d07208de592428c688d128682c0b051907e304a0a4d89a000842473308e0f84705869ac294141a16004a2184212308e0f0824d069ac2985c19d8d6712510c21091cc70784126834293)) else (if i<23 then (if i<22 then 0x1625518291186828792c9424a3c003cdaca251a55081d073d0e25d2c9204a163e02c14681da706029228696e1d071c5465d13861060b370f538311491434d65b801d8a26b3cc9a20089d0160630114669c16255182911868287992994b250000842475262dc705914b6c161a84c38d80010848ea5d1c164a22905b6c350e85adcd8c576084245d262dc7059288a4161a3f9b18aec108496e752e930b2511490c161a360012e9879a543aad07438e25d8392a32a3230a44e18419b8b40b18b6d381a69adc4212409c4c24e148902a0b04998a62f4d069a621091d4d85d5b93852240a9e8160929a685edb0d34c42123a984b04a148902a7a05824cc9a17869a6007f34d44a34aa103a0e2ebfc9446190a44a163c02c14682a8c1381a40adc3a0e2ea8c942913860f40b3734cb4316da7034815b801d0a269bf86e2075845027005818c10326a705895460a4461a0a194a4461d001ecd351255081d071c546f725118642912858f80b05190aa304e068d81d071c5464a1489c308305998b4316da7034d336001d0a269bd86e2075844e80b031b0b90326a705895460a4461a0a1e4a4461d0022ad351255081d071c4baa3230c852250b1f0160a3414460584e06a52b70e838e2a32e8a44e184182cdc5318961381a69adc00e85134e2a37103ac22740581a06602c125382c94a551829118682879328e88c0010848ea611b20c16296d86a1c46834300021091d4c25825118769a14b6c350e8641dd8db7408424612c1286c461da68521a3fbb1b6e810848ea58250d88c3b4d0a4346a51a60040251b1c04a36380946980118404a37b80946f40112c04a34c008241a0128dee150128e02340a8086a02002892e5e0f0681e823812d9235159ec609414995729d3600144c34b92c3c1a07a08e05e1a8acf6304a0a4d2584e9ccc2a213860f86e2382862a414c3834824cae000a2259ec60b814984b01a41274d4005130d2e350f3a8340f411c0bd02258acf63022a5052694e8002a734a18544a4148902a783312c5e452b86904995c0d61c7b1811452692b869049d43a89b6970e034e00b0217092e7198a93c93450a44c1a0b9ecce562006105233692d44d64ba14380d2e02c0849738cc549e8e24852260d05cf6672b9388082919b46aa269a5d0a1c06970160419b9c922a4f4712429130682e7b33c8cac384110cda004ba6116220998016073693dce3916a711c291186828525c8f000a28da5c380d05810931c198a93c94470a44c1a0b9ecce562020a6a6d108489cb81c0a44e1a0c169ae47058c52886108489cb81c0a4481a0a82c12536b8f5342f450842458252e0708f120682a0b04b5c7a9a17c3c528a10849704e228d11e29120682a0b04b5ca62f87b65340051465ae94428802260058189b1c1ba7058291186828773194878825c9b400a28ab5d else 0x166d966ac99aa44cc7538a36734d652066a9132b74e28d9ca459ad58cb251a61729d5226422d74f29166d7632c98ca44cc7538a363b4d65206329132204e28d8ea459ad4262f5a2605ee75928d30b94ea9166d773c8164a34c2e53ab273a91331d4e4a1472a2eb4d652073a9132114e28d48b398ad56e5e5ca74e4b64eadd3451692d00e0b85349680705bc214132f02640981102640b4048012e987f2543a0e8ca8d045d254d868270c1b8b4d92382c62294e0696e21091b0ba4e5b8e052240d054160929b647a9a1788424612c12870240d0541609330f5342f14b644212309388a341205416093314c5e294d069b2007b3654495420741c8237a8c94f71a49c4a1605828c8551f8c0529c0d1b03a0e2528c68d01386016662d3648e3114a70346c0033144f63a080220b031b0b84d680dd382c4aa3052230d05104772949c78008ab6544a34aa103a0e411bcba34938942c0b051a0b051948fc60294e0696e1d0717546346809c300b37160a6d9238c4529c0d2dc00cc51454e8200882c0c602c125a0374e0b12a8c1488c34143b994788293cd400f36ca894695420741c8237975e84a938942c0b051a0aa451d8c0529c0d2dc3a0e2ea8c94d013860166e6c9688a3d188a5381a5b80198a2799d0401105818c0d026914669c1625518291186828823b9964e52108490271272e07029120682a0b0494dae3d4d0bc42123a96094b81c0a4481a0a9e816096b8f5342f10848eab827114682912054f40b04b5ca69a17b6c3400513f8c02008a04e00b0313594374e0b12a8c1488c34143698ca4b91e001451530080227405818b049650dd382c4aa3052230d050f2631e2e4da00513ccc020089d01606651348a334e0b12a8c1488c34143c9b4c6b9291c944d94b9c0380d05810b849768cc549e480a44c1a0b9d4d25420254fe598c17944d74b970380d3801092ed198a92029130682e7d30950809505964d49e1aa89a697248701a7005811da5c198a93c901489834173e9a4a8384a90e30590025d31154a8741d0e3897632a32cc18689c13861066e2382c62296d869acb7311a84e184191c163114b6c34d6518012e982688826760581cc459768e45a9c1488c34143c995ac3c8741a1621091c4c238120541609330f5342f14b6c34818335a1621091d4ba381489034153d02c123d4d0bdb6d65b9b042123a98468240a9e81609332685e296d86a1c456b42c00fe6b2894695420741c5d2c921fe3412858f00b051a07e9c180a434815b8741c5d518d04e183d02cdcd623a7062296d86902b7003b144d67f1344011409c01606300dd382c4aa3052230d0524a652c94078007b3594495420741c715196490f71a4944a163e02c14641fa7060290d1b03a0e38a8c68270c20c166623a7062296d869ac6c003b144d67b13440113a02c0c6c2e4606e9c) else (if i<24 then 0xa51bfc26d37406946f709b4dd01a51bdc26d37406892ec4d215da461bb6d3422230dd34466da653a304c84d3a304c92d0f0e18265703009c3860990986860130d0c146e631ae614a37a08972e63a2d934823a2d9341341279dae751a60e1254ec994899103593c6085a7a4ce776a9132495ca7146f4523d646e973a8d309d73ba5489919ae5381551c050cd773855290f51c05491b2f8d2081546ca570354eca546f711359c42951bdc44d6710a546f411359c42951bd044b7710a4d4c671a8d30b94e89548991035d3ca47d1cdaec612c3a12e363291329c51b1c42d6718a6171151b1d48f5658950aec4d125da824d1d104d66b2682674413a5c6a34c2744aa47d048e6d3748684b0e83b8dd2a44ca702aa38088468d671854530688a8deea47c3f42a255ba68265194a8dee1369b7d46f71134dbec670a8d309d5ca9132116ba7949326bb19c2c6522640d224e28d8ed3708b5a8e14c28d8f2965a91dae151a613aa44c88022d64f185aced5243a0ce176a91320691271472e69b860f1116b51c2a38444946f7523e2304b4eae1343b110c1329d182649687830c045061826570304c8893a3091a913630110a46099110a4d43064a6448305c26844d64f2e134136b278e0a34c2c1c6e76b27902725c269729c121146ab84d2e538451aae134225ca71472d112e574a37fae574a37a2e574a37a08972ba66aed469893a7546980f3593ca45eb659abb66a9132b94e28d9cd65da8d9ca45eb01709a11180dad6302e1341336b590eb84d088c8d64f21d709a323a576a34c275469807b593ca45e849a6e90d4320ebb74a9132b94e05547011a35976158343e40e9522650a205ca702aa37fa917ac00aa605e9c5f84c5e9b70aed469802c893aa34c079ac9e522f5a6e1902ed469807a745ad470a6576e15226538b951cadacbb9038548994e2e548bd98b0146604e2e4e49d4c0bd3898110bd38bf17a6d46dd31ae620a37f84d72dd66b79469893a766aa49b17db2cd6f33548995ca7146ce69b7946ce524a5a2b876b79469819c953b265226422d64f182169e93379daa44ca15729c903b548995ca7253319328dfea48047d301317a723ea317a6dc6de51a613b206f28d301e4eb79c6a44c9c1729c1228df24a69b7849072c481c6a44c84492b94e09146f95244ce25f7e89262515c1c93b31302e53824948dd6c9a230dd6c9a111193cb64d0ec446005485321305485a4cf0382e20d26781c171078888c10b3682a4c133042cda0a9304c0ef10d02e209909868152009980340a9034a04870385416f18834a04071a85417101101c520b85088c0290548532221482a42d27d9c80e2405c29a4fb0392c480b853c5f6131202932134ec80149911276400a8c2e0c09b5cc9814a396089a6b151bfc26d358a8dee1369ac546f71134d62cd5928d31274ea9 else 0x51bdc44d96628dee136cb31473309b6598a37a089b2cc2c12d709a5ca7066a34c37988e96ba788a355c269729c0a9146ab84d2e5381551bfd72c551bfc26b962a8e60135cb1546f45cb14e0a34c38d60cd6b278e0ec4d3b5ac9c121b0bcb74d089ac9c19a8d30b2623a5ac9e19bb134ed6b2702a451aa6844d64e0548a356b2696e9c0aa8c9a896b3b146ff5bbb146ff09b59d8a37b889acec51bdc26d67628c9a896b3b146f411359d8a37a2ddd84d5ba68b24d5ba6826596da78bcb74d088a2db2f2dd341328b6d46ff09addd01)))))))
def pred511_11 := batchRange 511 raw511 cuts511 11 4 layer511_10 layer511_11 12
theorem cases511_11_0 : pred511_11 0=true := by decide +kernel
theorem cases511_11_12 : pred511_11 12=true := by decide +kernel
theorem cases511_11_24 : pred511_11 24=true := by decide +kernel
theorem cases511_11_36 : pred511_11 36=true := by decide +kernel
theorem cases511_11_48 : pred511_11 48=true := by decide +kernel
theorem cases511_11_60 : pred511_11 60=true := by decide +kernel
theorem cases511_11_72 : pred511_11 72=true := by decide +kernel
theorem cases511_11_84 : pred511_11 84=true := by decide +kernel
theorem cases511_11_96 : pred511_11 96=true := by decide +kernel
theorem cases511_11_108 : pred511_11 108=true := by decide +kernel
theorem cases511_11_120 : pred511_11 120=true := by decide +kernel
theorem cases511_11_132 : pred511_11 132=true := by decide +kernel
theorem cases511_11_144 : pred511_11 144=true := by decide +kernel
theorem cases511_11_156 : pred511_11 156=true := by decide +kernel
theorem cases511_11_168 : pred511_11 168=true := by decide +kernel
theorem cases511_11_180 : pred511_11 180=true := by decide +kernel
theorem cases511_11_192 : pred511_11 192=true := by decide +kernel
theorem cases511_11_204 : pred511_11 204=true := by decide +kernel
theorem cases511_11_216 : pred511_11 216=true := by decide +kernel
theorem cases511_11_228 : pred511_11 228=true := by decide +kernel
theorem cases511_11_240 : pred511_11 240=true := by decide +kernel
theorem cases511_11_252 : pred511_11 252=true := by decide +kernel
theorem cases511_11_264 : pred511_11 264=true := by decide +kernel
theorem cases511_11_276 : pred511_11 276=true := by decide +kernel
theorem cases511_11_288 : pred511_11 288=true := by decide +kernel
theorem cases511_11_300 : pred511_11 300=true := by decide +kernel
theorem cases511_11_312 : pred511_11 312=true := by decide +kernel
theorem cases511_11_324 : pred511_11 324=true := by decide +kernel
theorem cases511_11_336 : pred511_11 336=true := by decide +kernel
theorem cases511_11_348 : pred511_11 348=true := by decide +kernel
theorem cases511_11_360 : pred511_11 360=true := by decide +kernel
theorem cases511_11_372 : pred511_11 372=true := by decide +kernel
theorem cases511_11_384 : pred511_11 384=true := by decide +kernel
theorem cases511_11_396 : pred511_11 396=true := by decide +kernel
theorem cases511_11_408 : pred511_11 408=true := by decide +kernel
theorem cases511_11_420 : pred511_11 420=true := by decide +kernel
theorem cases511_11_432 : pred511_11 432=true := by decide +kernel
theorem cases511_11_444 : pred511_11 444=true := by decide +kernel
theorem cases511_11_456 : pred511_11 456=true := by decide +kernel
theorem cases511_11_468 : pred511_11 468=true := by decide +kernel
theorem cases511_11_480 : pred511_11 480=true := by decide +kernel
theorem cases511_11_492 : pred511_11 492=true := by decide +kernel
theorem cases511_11_504 : pred511_11 504=true := by decide +kernel
theorem cases511_11_516 : pred511_11 516=true := by decide +kernel
theorem cases511_11_528 : pred511_11 528=true := by decide +kernel
theorem cases511_11_540 : pred511_11 540=true := by decide +kernel
theorem cases511_11_552 : pred511_11 552=true := by decide +kernel
theorem cases511_11_564 : pred511_11 564=true := by decide +kernel
theorem cases511_11_576 : pred511_11 576=true := by decide +kernel
theorem cases511_11_588 : pred511_11 588=true := by decide +kernel
theorem cases511_11_600 : pred511_11 600=true := by decide +kernel
theorem cases511_11_612 : pred511_11 612=true := by decide +kernel
theorem cases511_11_624 : pred511_11 624=true := by decide +kernel
theorem cases511_11_636 : pred511_11 636=true := by decide +kernel
theorem cases511_11_648 : pred511_11 648=true := by decide +kernel
theorem cases511_11_660 : pred511_11 660=true := by decide +kernel
theorem cases511_11_672 : pred511_11 672=true := by decide +kernel
theorem cases511_11_684 : pred511_11 684=true := by decide +kernel
theorem cases511_11_696 : pred511_11 696=true := by decide +kernel
theorem cases511_11_708 : pred511_11 708=true := by decide +kernel
theorem cases511_11_720 : pred511_11 720=true := by decide +kernel
theorem cases511_11_732 : pred511_11 732=true := by decide +kernel
theorem cases511_11_744 : pred511_11 744=true := by decide +kernel
theorem cases511_11_756 : pred511_11 756=true := by decide +kernel
theorem cases511_11_768 : pred511_11 768=true := by decide +kernel
theorem cases511_11_780 : pred511_11 780=true := by decide +kernel
theorem cases511_11_792 : pred511_11 792=true := by decide +kernel
theorem cases511_11_804 : pred511_11 804=true := by decide +kernel
theorem cases511_11_816 : pred511_11 816=true := by decide +kernel
theorem cases511_11_828 : pred511_11 828=true := by decide +kernel
theorem cases511_11_840 : pred511_11 840=true := by decide +kernel
theorem cases511_11_852 : pred511_11 852=true := by decide +kernel
theorem cases511_11_864 : pred511_11 864=true := by decide +kernel
theorem cases511_11_876 : pred511_11 876=true := by decide +kernel
theorem cases511_11_888 : pred511_11 888=true := by decide +kernel
theorem cases511_11_900 : pred511_11 900=true := by decide +kernel
theorem cases511_11_912 : pred511_11 912=true := by decide +kernel
theorem cases511_11_924 : pred511_11 924=true := by decide +kernel
theorem cases511_11_936 : pred511_11 936=true := by decide +kernel
theorem cases511_11_948 : pred511_11 948=true := by decide +kernel
theorem cases511_11_960 : pred511_11 960=true := by decide +kernel
theorem cases511_11_972 : pred511_11 972=true := by decide +kernel
theorem cases511_11_984 : pred511_11 984=true := by decide +kernel
theorem cases511_11_996 : pred511_11 996=true := by decide +kernel
theorem cases511_11_1008 : pred511_11 1008=true := by decide +kernel
theorem cases511_11_1020 : pred511_11 1020=true := by decide +kernel
theorem cases511_11_1032 : pred511_11 1032=true := by decide +kernel
theorem cases511_11_1044 : pred511_11 1044=true := by decide +kernel
theorem cases511_11_1056 : pred511_11 1056=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_11 : settled 511 raw511 11 4 layer511_11 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_10 (width:=12) (groupsN:=89) (by decide +kernel) ⟨cases511_11_0,cases511_11_12,cases511_11_24,cases511_11_36,cases511_11_48,cases511_11_60,cases511_11_72,cases511_11_84,cases511_11_96,cases511_11_108,cases511_11_120,cases511_11_132,cases511_11_144,cases511_11_156,cases511_11_168,cases511_11_180,cases511_11_192,cases511_11_204,cases511_11_216,cases511_11_228,cases511_11_240,cases511_11_252,cases511_11_264,cases511_11_276,cases511_11_288,cases511_11_300,cases511_11_312,cases511_11_324,cases511_11_336,cases511_11_348,cases511_11_360,cases511_11_372,cases511_11_384,cases511_11_396,cases511_11_408,cases511_11_420,cases511_11_432,cases511_11_444,cases511_11_456,cases511_11_468,cases511_11_480,cases511_11_492,cases511_11_504,cases511_11_516,cases511_11_528,cases511_11_540,cases511_11_552,cases511_11_564,cases511_11_576,cases511_11_588,cases511_11_600,cases511_11_612,cases511_11_624,cases511_11_636,cases511_11_648,cases511_11_660,cases511_11_672,cases511_11_684,cases511_11_696,cases511_11_708,cases511_11_720,cases511_11_732,cases511_11_744,cases511_11_756,cases511_11_768,cases511_11_780,cases511_11_792,cases511_11_804,cases511_11_816,cases511_11_828,cases511_11_840,cases511_11_852,cases511_11_864,cases511_11_876,cases511_11_888,cases511_11_900,cases511_11_912,cases511_11_924,cases511_11_936,cases511_11_948,cases511_11_960,cases511_11_972,cases511_11_984,cases511_11_996,cases511_11_1008,cases511_11_1020,cases511_11_1032,cases511_11_1044,cases511_11_1056,True.intro⟩
def layer511_12 : Layer := (247,13,7,3,83,309,6,8,(fun i => (if i<4 then (if i<2 then (if i<1 then 0xff91a40fff95840fff92840fff91840fff92540fff91540ffed5888bfed3888bfed1888bfed3588bfed1588bfed1388affeaa44b7fd9a44affd8a44affd5a44affd3a44b7fd8944b7fd5944b7fd3944bbfe8844bf7e5544bfbd4544bfde3344bff51344bff90344bff558847ff538847ff528847ff535847ff525847ff5238467feaa6267feaa5667feaa4e67feaa4a67feaa4673fd59a233fd39a233fd29a233fd19a227fd9a5627fd9a4e27fd9a4a27fd9a46377d8995777d3995777d2995777d19957b7e88956fbeaa5177bd895177bd29517bbe885167fd9a4d7f3d454d67fd9a4967fd9a456fbeaa452fbd5a4537bd894537bd29453bbe88453f3e554537dd898cf7dd598cf7dd298cf7dd198cfbde888cff5e558cff9d458cff9d148ce7fd9a48e7fd9a44ffb51444effaaa40f7f98940f7f92940fbfa8840ff7a5540ffb94540ffd93540ffb91440ffd91340f7ed8988b7ed5988b7ed3988b7ed1988bbee8888bf6e5588bfad4588bfad1488bfce3388bfe90388a7fd9a44b7f5898477f5598477f5398477f529847bf688847f7655847fb545847fd633847ff103847fe62284540eb05b4a99f5ed061f26b87f1ad539b2c489f9547b499c86aa834bf1eedd3d77bb4e8751674100a83755a6804173b49f5461073b5f404df6e22188283bb59a98fbe623ac50d4c781806f56a345672e4f575f0c90f0c5a26d0fc18a511a2219ad8072b1f94465511768b556d89f946263942d55aee9731c94dee62d03dd7a722c54f56dda922c4c0c0e00f3e4ec45e934f102a49016381f508147fe5fa1cc53523cfb0bceb662af052ae8a8855a5c6dd4de00f703de78d12424643833e321ee875db2f093ec9e80f77bb881d03dea50b93ee3d282eb2603dc58103dc0f7bd1d3cd91c74dad5e72516a1c0f787d994203ddee1be480f79c6d666e1238e703dc0f703dc0f70f02e62dd640f703dc0f700140f7f45563803dc0f777700f7a3280f7db5bf3f2a084ce6ac00f72e200f74a0c8a43d0e4f103dc636b5afaa3b31704def6076703de92a03dc0934fcc0f703decec03dc0f720dc0f74b20bc2fe3ffbe23880f703dcd6c03deb072ccc0f703dc0f703dd98c03dc0f703dc0f7225333a94b38af03dfae003de18003dc0f703dc9c403dc0f703dc0f7626e10856c996a3a597d54f9a6a04e3be1119c1b258d10a9af027bacf7a80f7c3acc4b68107a103dcd2403dc0f703dcab703de5955153010e37a384246843bda9865e740cd417d8f1e92ecf58a16fca9e8e440f75f5c329db912d9d67156903dc1f281840f71c86abbbbd089812b422e177eee81cd5b121665e0290284c728c59dbf6f4bd1c78ccf4014c0921020001c0091c8011b14011fd43398e9901b8c624a3d11c6100084dcb2410490400002891c60010ca0890955811004000012801c2000080002 else 0x489027088210802307a1e0761d0721c07c1a0641806c1784c12846110421004c0f82c0a826090220802c060140401e02806020029750fa67d24e8af4179ecce766af31f972cab64df2318fac6a62d312b876c2860a70177ecbe6dea6f0b75fb9fdc7adff6dbb5cda6acf965cb1c5852be15caad5d632ad9547a90d3ea9b94bea4f51ea8ad431a06cfda7a93b19c74daa6a5330986cbaa58f2af946c9aa491231906c7d63a51af8c5c5d22b7142894c4361e30d4858c2660f10558194039feafdd7e2be85f12f697a2bc89dfeee6767bae1d2ae7f72fb939c56e086f2b731b6ad9e6c0b591a90d2b68733d19b4cc065332318d0c5061830417dabca5d42e3d6f0b5f5a12c99606aeb565aaad510a64520a8a14229f84eda70d3589954bf259d29893048b23f11c28c8457a2590fa864425a09d0207f03e81ebcf187693a39cb8e2a6f836f1b18d5669233c9980c8e62e30a97f8bcc5ce2db967cb105712ad150ca5a51828113b09aa4be25392408f046222790f08524142008fac7aa3bf1d68e6870e3741b08d246623191808ba45a22bd1548a504fe26c12c892447222710a88083e81e10e986f034a18e0bb857c28e13409084241ee0e106502cc138085036815408402a00c0003ffd3a563ffd2a563ffd1a563ffd5a4e3ffd2a4e3ffd1a4e3ffeaa4a3ffd5a4a3ffd3a4a3ffd1a4a3ffd5a463ffd3a463ffd2a463ffeaa4d7ffd8a4d7ffd2a4d7ffd1a4d7ffd284d7ffd184d7ffd8a497ffd3a497ffd1a497ffd38497ffd18497ffeaa457ffd8a457ffd3a457ffd2a457ffd38457ffd28457ffd8a48fffd5a48fffd1a48fffd5848fffd1848fffd1548fffeaa44fffd8a44fffd5a44fffd2a44fffd5844fffd2844fffd2544fffd8a44bffd5a44bffd3a44bffd5844bffd3844bffd3544affeaa5637fd9a5637fd395637fd295637fd19562ffeaa4e37fd9a4e37fd594e37fd294e37fd194e2ffeaa4a37fd9a4a37fd594a37fd394a37fd194a3bfd384a2ffeaa4637fd9a4637fd594637fd394637fd29463bfd28463f7d38957f7d28957f7d18957fbd38517fbd28517fbd18516ffeaa4d77fd9a4d6ffd8a4d77fd894d77fd294d77fd194d7bfe884d7f7d584d7fdd384d6ffeaa4977fd9a496ffd8a4977fd894977fd394977fd19497bfe88497fed28497f7d35496ffeaa4577fd9a456ffd8a457fbd4a4577fd894577fd394577fd29457bfe88457ff518457f7d25457fbd58453fbd38453fbd28453fbd35453fbd25453fdd588cffdd288cffdd188cffdd258cffdd158ceffeaa48f7fd9a48effd8a48effd5a48f7fd8948f7fd5948f7fd1948fbfe8848ffed2848ff7e5548ffbd4548ffbd1448effeaa44f7fd9a44effd8a44effd5a44f7fd8944f7fd5944f7fd2944fbfe8844fff51844ff7e5544ffbd4544ffdd2344fff98a40fff95a40fff92a40f) else (if i<3 then 0x24511a3011093c28551d013538484c16150e0d445b02062f25501a30471109285b551d0138354e16150e0d3d4202062f25501a304711093c551d0135384e16150e0d445b02292d0625501a304711093c5b55280138354e16150e0d44022f231e06501a00474c480102343538140c402c2116150e0d44062f25521a003c423d01023435384b140c2c214e16150e0d062f25521a551801023435383c5b4e16150e0d3d422f25501a551801023435385b1d4e16150e0d442f1e23501a450f073a541b4e16150e0d44063502382b2e25501a450f073a54264e16150e0d44063502382f2024501a031b0455224f345b4e16150e0d4435382f501a000203171934514e16150e0d447e0635382f2530557e484c16150e0d445b0635382f2530557e4e16150e0d445b063538292d2500024c488005345116150e0d440635382f250002423d800534514e16150e0d0635382f251755037e04345b4f4e16150e0d3d4235382f25174f7e514e16150e0d3d42062f251755037e04345b4f4e16150e0d4435382f231e174f7e514e16150e0d44062f231e2611093c32551d012e2b484c16150e0d4402063925501a2647110932551d012e2b4e16150e0d3d4202063925501a264711093c551d012e2b4e16150e0d440233370625501a264711093c5532012e2b4e16150e0d440239231e06501a00474c4801022a2e2b140c40362116150e0d44063925521a003c423d01022a2e2b4b140c36214e16150e0d063925521a551801022e2b3c364e16150e0d3d423925501a551801022e2b361d4e16150e0d44391e23501a0032333701022a2e2b4b140c40214e16150e0d440625521a7f0401022e2b32504e16150e0d4406333725450f073a54304e16150e0d44065b392b022e2024501a1b11093c325528012420484c16150e0d440206392f501a1b4711093255280124204e16150e0d3d420206392f501a1b4711093c55280124204e16150e0d44023337062f501a1b4711093c55320124204e16150e0d4402392d2906501a00474c4801021f2420140c40362c16150e0d4406392f521a003c423d01021f24204b140c362c4e16150e0d06392f521a5518010224203c364e16150e0d3d42392f501a0032333701021f24204b140c402c4e16150e0d44062f521a7f040102202432504e16150e0d440633372f00282d2901021f24204b140c40364e16150e0d440639521a1ec7a1e0741a86919c661946418c621846017c5d16c5a1605791d4711c4691545116445104410d4210a4150441901401003f0f83d0f03b0e8390e0370d8350d0300b82d0b02b0aa294a4292a02889d2709ca60982408a21084a00801f8781e2741d84d1304e12c461144411c42104430fa3e0f63d0f23c0fc3a0e4380ec368d8358d4348d0370c8310cc2e8b82d8b42c8b02f0a8290ac26898258942 else 0x9553c261b5a4a130b3f0531194e16150e0d44023337062b2e2024501a000246474c51130b3f053519140c40362a1f160e062e20245200023b3c42514a130b0535194b140c362a1f160e062e202452546155185a4f4a130b3b9f35193c364e16150e0d3d42392b2e2024501a00023132375b514a130b3f05194b140c402a1f160e062e20245291275998314b140c40322a4e16150e0d440633372b2e521a7fa37e045a4f4a130b3f053150324e16150e0d440633372e2b24201c50120a0433291801021f2447140c3c362c4c3d160e4206521c50120a3d04291801021f2447140c40322c4c33160e0637521c50120a3d04331801021f2447140c4036284c29160e062d521c5048120a04291801021f244b140c3c322c160e42330637521c5048120a04331801021f244b140c3c3628160e4229062d521c5048120a3d041801021f244b140c403228160e0629372d52000f073a30261b4a4d16150e0d44540206395b2f25511a00450f0730268a1b544e16150e0d3f430206395b2f25511a00450f073a2684541b534e16150e0d44023538062f25511a00450f073a301b4e16150e0d445402395b2b2e0625511a00450f073a308126544e16150e0d4402395b2f242006511a454d11093228551d014a16150e0d3d420206392f25501a454d11093c28551d014a16150e0d44023337062f25501a454d11093c32551d014a16150e0d440239292d0625501a454d11093c325528014a16150e0d4402392f231e06501a0f073026541b4a4d16150e0d3f430206395b2f25501a0f073a26541b4a4d16150e0d44020635382f25501a0f073a301b4a4d16150e0d44540206395b2b2e25501a0f073a3054264a4d16150e0d440206395b2f2024501a3a11093228551d01433f484c16150e0d0206392f25501a3a47110928551d01433f4e16150e0d023337062f25501a3a47110932551d01433f4e16150e0d0239292d0625501a3a47110932552801433f4e16150e0d02392f231e06501a00474c4801023e433f140c362c2116150e0d06392f25521a0002038a173e36544e3f16150e0d0543395b2f25511a3a325419484c0516150e0d3f43395b2f254f1a3a3254194e16150e0d3f43395b292d05254f1a00024c4856193e3616150e0d3f43392f25511a450f0726541b4e16150e0d3f43020635382f25501a033a0455414f345b4e16150e0d35382f25501a450f0730541b4e16150e0d3f430206395b2b2e25501a450f073054264e16150e0d3f430206395b2f2024501a000281031736541f4e16150e0d44395b2f200524511a1736544e16150e0d3d0542395b2f2024511a321b5419484c0516150e0d44395b2f20244f1a321b54194e16150e0d44395b2d290520244f1a00024c485619361f16150e0d44392f2024511a0002423d5619361f4e16150e0d392f20)) else (if i<6 then (if i<5 then 0x62b382e525455185f4f4a130b3b9f20195b3c344e16150e0d3d4235382b2e25501a5455185f4f4a130b3f1c195b341d4e16150e0d4435382b2e1e23501a0054724f4610083b031c7327174b140c40342c1f4e16150e0d44350602382f2024521a4711093c5b55286d4e9d16150e0d44020635382f2024501a544f10083b0398271747140c40342c1f484c16150e0d44063502382f2024521a544f461008039827174b140c3c342c1f4e16150e0d3d42063502382f2024521a547211093c3055281b9746130b3f059f2b19484c16150e0d445b020635382f2024501a548a72471109305b55281b974a130b3b059f2b194e16150e0d3d42020635382f2024501a5472471109553c301b914a130ba03f0527194e16150e0d445b023538292d062024501a000246474c51130b3f052b19140c40342c1f160e06203824528e31469847140c40342c484c16150e0d440635382f521a00023b3c42514a130b052b194b140c342c1f160e0620382452545518974f4a130b3b9f2b193c345b4e16150e0d3d4235382f2024501a5e1c91a0274b140c40281f4e16150e0d4406292d2024521a120a3d04291e6c3451484c16150e0d449a7e0635382f2548120a04291e6c34514e9e16150e0d3d427e0635382f2548120a3d041e6c34514e16150e0d449a7e063538292d2548120a3d04296c34514e9e16150e0d447e0635382f231ea47e6a4f120a0431291e80053451484c16150e0d3d420635382f25937e5b4f120a3d04311e80059e3451484c16150e0d44063538292d258f7e4f120a3d04312980053451484c16150e0d440635382f231e887e4f48120a04311e800534514e16150e0d3d42063538292d257e4f48120a5b04312980059a34514e16150e0d3d420635382f231e2750120a04331e1801022a2e47140c3c36214c3d160e4206522750120a3d041e1801022a2e47140c4032214c33160e0637522750120a3d04331801022a2e47140c40361d4c1e160e062352275048120a041e1801022a2e4b140c3c3221160e4233063752275048120a04331801022a2e4b140c3c361d160e421e062352275048120a3d041801022a2e4b140c40321d160e061e3723520054574f4610083b035958311c174b140c40362a1f4e16150e0d4406392b022e2024521a4711093c553258594e16150e0d440206392b2e2024501a544f10083b0398311747140c40362a1f484c16150e0d4406392b022e2024521a544f461008039831174b140c3c362a1f4e16150e0d3d4206392b022e2024521a91544f461008983b03174b140c40322a1f4e16150e0d440633372b022e2024521a54945711093c5532261b5a46130b3f059f3519484c16150e0d440206392b2e2024501a548a574711095532261b5a4a130b3b059f35194e16150e0d3d420206392b2e2024501a5484574711 else 0x93a3226551d8946130b0535a12019484c16150e0d3f430206392b2e25501a548476854711093a26551d894a130b053120194e16150e0d3f43023337062b2e25501a548176824711093a553226894a130b05351c194e16150e0d3f4302392b2e231e06501a000246474c51130b05352019140c3e362a21160e432b062e523b8746a147140c3e3621484c16150e0d3f43063925521a278731994b140c322a214e16150e0d0633372b2e25521a0054744f4610081c03317527174b140c3e362c1f4e3f16150e0d024306392f2024521a4711093255286d4e16150e0d3f430206392f2024501a544f1008033198271747140c3e362c1f484c16150e0d3f024306392f2024521a55186e364e16150e0d3f43392f2024501a947411093a3255281b9a46130b540535a12b19484c16150e0d3f430206392f2024501a548474854711093a55281b9a4a130b05312b194e16150e0d3f43023337062f2024501a92744711093a55321b9a4a130b5405a03527194e16150e0d3f4302392d29062024501a000246474c51130b05352b19140c3e362c1f160e43200624528e3b469847140c3e362c484c16150e0d3f4306392f521a871c99274b140c36281f4e16150e0d0639292d2024521a54606a4f120aa233291c185619361f484c16150e0d3d42392f2024511a65544f120aa23d291c185619325b1f484c16150e0d4433372f2024511a6083544f120a3d331c185619361f484c16150e0d4439292d2024511a9b544fa248120a291c185619325b1f4e16150e0d3d4233372f2024511a885460834f48120a331c185619361f4e16150e0d3d4239292d2024511a315b50120a04291e180102343847140c3c2c214c3d160e420652315b50120a3d041e180102343847140c4028214c29160e062d52315b50120a3d0429180102343847140c402c1d4c1e160e062352315b5048120a041e18010234384b140c3c2821160e4229062d52315048120a5b042918010234384b140c3c2c1d160e421e06235200545c4f4610083b03275e5d1c174b140c40342a214e16150e0d44350602382b2e25521a4711093c5b551d5d5e4e16150e0d44020635382b2e25501a93544f10083b031c1747140c40342a21484c16150e0d44063502382b2e25521a544f46100803991c174b140c3c342a214e16150e0d3d42063502382b2e25521a545c11093c3026551d5f46130b3f059f2019484c16150e0d445b020635382b2e25501a545c47110930265b551d5f4a130b3b059f20194e16150e0d3d42020635382b2e25501a545c4711095b553c30265f4a130b3f051c194e16150e0d440235382b2e231e06501a000246474c51130b3f052019140c40342a21160e062b382e5293315e4647140c403421484c16150e0d4406353825521a00023b3c42514a130b0520194b140c342a21160e) else (if i<7 then 0x1d63644a4d16150e0d44020635382f25501a546245110930285b551d66130b3b052b20194a4d16150e0d3d42020635382f25501a54624511093c30551d66130ba23f052720194a4d16150e0d445b023538292d0625501a54624511093c305b552866130ba23f052b1c194a4d16150e0d440235382f231e06501a00547c4f2710083b03317d1c17494a140c40362a21024d16150e0d4406392b2e25521a11093c32551d6f4a4d16150e0d449c020639962b2e25501a548a7c8b4511093226551d130b3b053520194a4d16150e0d3d420206392b2e25501a54847c854511093c26551d93130b3f053120194a4d16150e0d44023337062b2e25501a54817c824511093c553226130b3f05351c194a4d16150e0d4402392b2e231e06501a64279331140c40322a2116150e0d440633372b2e25521a00547a4f1c10083b03318e7b2717494a140c40362c1f024d16150e0d4406392f2024521a11093c3255288e6d4a4d16150e0d449c0206392f2024501a548a7a8b4511093255281b90130b3b05352b194a4d16150e0d3d420206392f2024501a54847a854511093c55281b90130b3f05312b194a4d16150e0d44023337062f2024501a548d927a4511093c55321b90130b3f05a03527194a4d16150e0d4402392d29062024501a1c8ea027140c4036281f16150e0d440639292d2024521a3b50120a04291e1801023e4347140c322c214c33160e0637523b50120a04331e1801023e4347140c3628214c29160e062d523b50120a0433291801023e4347140c362c1d4c1e160e06235265544f120a3b291e1856193e325b484c16150e0d3f4333372f25511a618c544f120a3b331e1856193e36484c16150e0d3f4339292d25511a8f54618c4f120a3b33291856193e36484c16150e0d3f43392f1e23511a0054784f461008310327791c174b140c3e342c214e3f16150e0d02430635382f25521a471109285b551d704e9d16150e0d3f43020635382f25501a95544f10080327991c1747140c3e342c21484c16150e0d3f02430635382f25521a547811093a3028551d9546130b052ba12019484c16150e0d3f435b020635382f25501a54784711093a30551d9ba24a130b052720194e16150e0d3f435b023538292d0625501a5481784711093a305b55289ba24a130b052b1c194e16150e0d3f430235382f231e06501a000246474c51130b052b2019140c3e342c21160e4335063852693195469947140c342c21484c16150e0d0635382f25521a643b9546a147140c3e2c21484c16150e0d3f43062f25521a0054764f46100827033187771c174b140c3e362a214e3f16150e0d024306392b2e25521a47110932551d876f4e16150e0d3f43020639962b2e25501a544f10080331991c1747140c3e362a21484c16150e0d3f024306392b2e25521a5486947611 else (if i<8 then 0x4399249a5250120a043329186d48150d6e0639982f1a4c47140c3e36a02c1f160e439924525048120a0429186d4e150d6e06332f1aa14b140c3e32a02c1f98160e43992437525048120a0433186d4e150d6e0639291aa14b140c3e362d281f98160e4324529864637550120a3b04291c185146130b5b05312b1947140c3e322c1f064c160e43243752987d7550120a3b04331c185146130b060535271947140c3e36281f4c160e432d2452935b6f50120a3d041e185e48150d44251a524c47140e0c40342e2a211606385b6f5048120a041e185e4e150d3d251a524b140e0c3c342e2a2116420638915b6f5048120a3d04185e4e150d441e1a524b140e0c40342e2a1d169f062338995e685d5b50120a0431271e185146130b3b05201947140c3c342e2a214c52160e420638985e7b5d5b50120a3d043127185146130b3f051c1947140c40342a1d4c2e52160e062338985e755d5048120a5b04312718514a130b3b051c194b140c3c342a1d160e422e062338525b725048120a3d04201c73293135186d4e150d442f1a4b16140c40342c1f980e9706243852915b50120a3d0429186d48150d442f1a4c4716140c40342c1f0e0624a03852985b5048120a0429186d4e150d3d2f1a4b16140c3c342c1f0e420624a03852985b5048120a3d0418916d4e150d44291a4b16140c4034281f980e9f062438522d99986968735b50120a0431291c185146130b3b052b1947140c3c342c1f164c0e4206243852987d735b9650120a3d04311c189d51a046130b3f05271947140c4034281f164c0e062438522d99988777735b965048120a04311c18514a130ba03b0527194b140c3c34281f160e420624382d526d50120a3d0433185948150d4406391a4c47140c40362e2a1f160e2498526d5048120a043318594e150d3d06391a4b140c3c362e2a1f160e42249852916d5048120a3d0418594e150d984406331a4b140c40322a1f160e9f242e3752999859685850120a0433271c185146130b3b060535194c47140c3c362e2a1f160e4224529859635850120a3d04271c185b5146130b3f0531194c47140c40322a1f062e160e24375299985979585048120a04271c185b514a130b3b0531194b140c3c322a1f160e42062e2437520054674f3b100803312769681c17494a140c3e362c21024d16150e0d3f4306392f25521a11093228551d68694a4d16150e0d3f430206392f25501a5484674511093a28551d6b130b05312b20194a4d16150e0d3f43023337062f25501a5492674511093a32551d6b130b05a2352720194a4d16150e0d3f430239292d0625501a5481674511093a3255286b130b05a2352b1c194a4d16150e0d3f4302392f231e06501a0054624f3110083b032764631c17494a140c40342c21024d16150e0d440635382f25521a11093c285b55 else 0x957150120a04291e1869150d06332f99251a4d49140c3e322c2116520e43a2377150120a04331e1869150d063929251a4d49140c3e362d282116520e43997150120a0433291869150d06392f1e1a4d49140c3e362c1d16520e439923955b7050120a04291e1864150d3d2f251a524d4916140c3c342c21060e42a238935b7050120a3d041e1864150d4429251a524d4916140c40342821062d0e385b7050120a3d04291864150d442f1e1a524d4916140c40342c1d060e23387c502b27120a3d0433464a7d1e186f150d440639251a524d49140c40362e2a21160e9350120a04331e186f150d3d0639251a524d49140c3c362e2a21160e4250120a3d041e18936f150d440633251a524d49140c40322a21162e0e3750120a3d0433186f150d4406391e1a524d49140c40362e2a1d160e2350120a043329188e6d150d3d06392f1a4d4916140c3c362c1fa0520e42249850120a3d0429188e6d150d4406332f1a4d4916140c40322c1fa0520e98243750120a3d0433188e6d150d440639291a4d4916140c40362d281f520e24985b785048120a3531043b3f29791e18704e150d2f251a4b140e0c3e342c2195164306999b38525b50120a04291e18957048150d2f251a4c47140e0c3e342c2116430699a238525b5048120a041e18704e150d29251a4b140e0c3e34282199a11643062d38525b5048120a042918704e150d2f1e1a4b140e0c3e342c1da116430699233852997d795b9c50120a3b04311e189d5146130b05a127201947140c3e3428214c160e06432d385298998e7b795b9c50120a3b043129185146130b052ba11c1947140c3e342c1d4c160e064323385250120a04331e18876f48150d0639251a4c47140e0c3e362e2a21164399525048120a041e18876f4e150d0633251a4b140e0c3e322a21a116432e9937525048120a043318876f4e150d06391e1a4b140e0c3e362e2a1da116439923529964637750120a3b04271e185b5146130b0531201947140c3e322a21064c2e160e4337529899877b7750120a3b043327185146130b0605351c1947140c3e362a1d4c2e160e432352745048120a201c043375293b3f186d4e150d6e06392f1a4b140c3e362c1f98160e))))))
def pred511_12 := batchRange 511 raw511 cuts511 12 3 layer511_11 layer511_12 4
theorem cases511_12_0 : pred511_12 0=true := by decide +kernel
theorem cases511_12_4 : pred511_12 4=true := by decide +kernel
theorem cases511_12_8 : pred511_12 8=true := by decide +kernel
theorem cases511_12_12 : pred511_12 12=true := by decide +kernel
theorem cases511_12_16 : pred511_12 16=true := by decide +kernel
theorem cases511_12_20 : pred511_12 20=true := by decide +kernel
theorem cases511_12_24 : pred511_12 24=true := by decide +kernel
theorem cases511_12_28 : pred511_12 28=true := by decide +kernel
theorem cases511_12_32 : pred511_12 32=true := by decide +kernel
theorem cases511_12_36 : pred511_12 36=true := by decide +kernel
theorem cases511_12_40 : pred511_12 40=true := by decide +kernel
theorem cases511_12_44 : pred511_12 44=true := by decide +kernel
theorem cases511_12_48 : pred511_12 48=true := by decide +kernel
theorem cases511_12_52 : pred511_12 52=true := by decide +kernel
theorem cases511_12_56 : pred511_12 56=true := by decide +kernel
theorem cases511_12_60 : pred511_12 60=true := by decide +kernel
theorem cases511_12_64 : pred511_12 64=true := by decide +kernel
theorem cases511_12_68 : pred511_12 68=true := by decide +kernel
theorem cases511_12_72 : pred511_12 72=true := by decide +kernel
theorem cases511_12_76 : pred511_12 76=true := by decide +kernel
theorem cases511_12_80 : pred511_12 80=true := by decide +kernel
theorem cases511_12_84 : pred511_12 84=true := by decide +kernel
theorem cases511_12_88 : pred511_12 88=true := by decide +kernel
theorem cases511_12_92 : pred511_12 92=true := by decide +kernel
theorem cases511_12_96 : pred511_12 96=true := by decide +kernel
theorem cases511_12_100 : pred511_12 100=true := by decide +kernel
theorem cases511_12_104 : pred511_12 104=true := by decide +kernel
theorem cases511_12_108 : pred511_12 108=true := by decide +kernel
theorem cases511_12_112 : pred511_12 112=true := by decide +kernel
theorem cases511_12_116 : pred511_12 116=true := by decide +kernel
theorem cases511_12_120 : pred511_12 120=true := by decide +kernel
theorem cases511_12_124 : pred511_12 124=true := by decide +kernel
theorem cases511_12_128 : pred511_12 128=true := by decide +kernel
theorem cases511_12_132 : pred511_12 132=true := by decide +kernel
theorem cases511_12_136 : pred511_12 136=true := by decide +kernel
theorem cases511_12_140 : pred511_12 140=true := by decide +kernel
theorem cases511_12_144 : pred511_12 144=true := by decide +kernel
theorem cases511_12_148 : pred511_12 148=true := by decide +kernel
theorem cases511_12_152 : pred511_12 152=true := by decide +kernel
theorem cases511_12_156 : pred511_12 156=true := by decide +kernel
theorem cases511_12_160 : pred511_12 160=true := by decide +kernel
theorem cases511_12_164 : pred511_12 164=true := by decide +kernel
theorem cases511_12_168 : pred511_12 168=true := by decide +kernel
theorem cases511_12_172 : pred511_12 172=true := by decide +kernel
theorem cases511_12_176 : pred511_12 176=true := by decide +kernel
theorem cases511_12_180 : pred511_12 180=true := by decide +kernel
theorem cases511_12_184 : pred511_12 184=true := by decide +kernel
theorem cases511_12_188 : pred511_12 188=true := by decide +kernel
theorem cases511_12_192 : pred511_12 192=true := by decide +kernel
theorem cases511_12_196 : pred511_12 196=true := by decide +kernel
theorem cases511_12_200 : pred511_12 200=true := by decide +kernel
theorem cases511_12_204 : pred511_12 204=true := by decide +kernel
theorem cases511_12_208 : pred511_12 208=true := by decide +kernel
theorem cases511_12_212 : pred511_12 212=true := by decide +kernel
theorem cases511_12_216 : pred511_12 216=true := by decide +kernel
theorem cases511_12_220 : pred511_12 220=true := by decide +kernel
theorem cases511_12_224 : pred511_12 224=true := by decide +kernel
theorem cases511_12_228 : pred511_12 228=true := by decide +kernel
theorem cases511_12_232 : pred511_12 232=true := by decide +kernel
theorem cases511_12_236 : pred511_12 236=true := by decide +kernel
theorem cases511_12_240 : pred511_12 240=true := by decide +kernel
theorem cases511_12_244 : pred511_12 244=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_12 : settled 511 raw511 12 3 layer511_12 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_11 (width:=4) (groupsN:=62) (by decide +kernel) ⟨cases511_12_0,cases511_12_4,cases511_12_8,cases511_12_12,cases511_12_16,cases511_12_20,cases511_12_24,cases511_12_28,cases511_12_32,cases511_12_36,cases511_12_40,cases511_12_44,cases511_12_48,cases511_12_52,cases511_12_56,cases511_12_60,cases511_12_64,cases511_12_68,cases511_12_72,cases511_12_76,cases511_12_80,cases511_12_84,cases511_12_88,cases511_12_92,cases511_12_96,cases511_12_100,cases511_12_104,cases511_12_108,cases511_12_112,cases511_12_116,cases511_12_120,cases511_12_124,cases511_12_128,cases511_12_132,cases511_12_136,cases511_12_140,cases511_12_144,cases511_12_148,cases511_12_152,cases511_12_156,cases511_12_160,cases511_12_164,cases511_12_168,cases511_12_172,cases511_12_176,cases511_12_180,cases511_12_184,cases511_12_188,cases511_12_192,cases511_12_196,cases511_12_200,cases511_12_204,cases511_12_208,cases511_12_212,cases511_12_216,cases511_12_220,cases511_12_224,cases511_12_228,cases511_12_232,cases511_12_236,cases511_12_240,cases511_12_244,True.intro⟩
def layer511_13 : Layer := (23,10,7,2,8,29,5,5,(fun i => 0x5f494284dac89d21633ee2e94b39a6103c1106f32a547dd4942c012c89d216342d2e94b39a6103c61b6eb2a547d250b004da274858d0b8aa52ce69840f186f2cc2951f95250b004dac74858d0b8ba12ce69840f186f328a751f4ca50a12c89d31633ed2e95069840f0441b6eb2a547e34ca50a13689d31633ee2a95069840f0441bcb30a547d3294284dac74c58cfb8ba141a6103c1106f328a751f6d32942c012274c58d0b4aa541a6103c61b6eacc2951f4ca50b004b1d316342d2e85069840f186dbaca29d47d94ca50b004d9d316342e2a85069840f186f2cc229d479223ed2b5a12ce69840f1821bcca949f212234ad685069840f044086f32a527c8488fab5a141a6103c60b6e86ca949f21223ed5685069840f182f2cc06a527c8488fb55ab41a6103c60bcca688749e00324f296342e2e91a6103c61bcca951e002fc504c58ce2e95069840e1bcca951f59cfb941a6103c113cca949f59ce2141a6103c6f328a749e002d36ecc58d0ae95069840f186ca951f804d5341a6103c61b6eb2a000aac2d316342e2541a6103c61bca547800a09a3316342e2f41a6103c61bccd4791c88401489c421e09c4423100843d1e0f8703a1a8d06c30190b4582e140a84a2413080441d0e078301a0b84822100903c14090402808070080600338ba107c9d56dd9a5f15f50524418f1370c72c89d21c71184510ec2c05800ffeac7ff4e3ffa51ffd18ffe9afff497ffa2bffd23ffe89fff44affb137fd59bfe9cdff4a6ffa33bfe88fbf2afef517f7a29fde33ffc81ffb88bfec22a05911445900bf1202f7a80bc8d15005eb846e8cb01cdad23828e4fe6126593903f7f4102e95b35817904a00288a))
def pred511_13 := batchRange 511 raw511 cuts511 13 2 layer511_12 layer511_13 4
theorem cases511_13_0 : pred511_13 0=true := by decide +kernel
theorem cases511_13_4 : pred511_13 4=true := by decide +kernel
theorem cases511_13_8 : pred511_13 8=true := by decide +kernel
theorem cases511_13_12 : pred511_13 12=true := by decide +kernel
theorem cases511_13_16 : pred511_13 16=true := by decide +kernel
theorem cases511_13_20 : pred511_13 20=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_13 : settled 511 raw511 13 2 layer511_13 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_12 (width:=4) (groupsN:=6) (by decide +kernel) ⟨cases511_13_0,cases511_13_4,cases511_13_8,cases511_13_12,cases511_13_16,cases511_13_20,True.intro⟩
def layer511_14 : Layer := (1,5,7,1,1,2,0,1,(fun i => 0xf04020d0b090710058403820e010c0a08110600000983ff501e01))
def pred511_14 := batchRange 511 raw511 cuts511 14 1 layer511_13 layer511_14 4
theorem cases511_14_0 : pred511_14 0=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem solved511_14 : settled 511 raw511 14 1 layer511_14 :=
  advanceBatch pairs511 (raw_faithful 511 _ _) cert511 solved511_13 (width:=4) (groupsN:=1) (by decide +kernel) ⟨cases511_14_0,True.intro⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extra511 : Lower (roots 511 true) (graphGoal 511) 15 := by
  apply finishAug (cap:=14) 0x8020080201020080210 (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) ordinaryFull
  have eq : (nodeValues raw511 1 (nodeBits layer511_14 1 raw511.length 0)).toFinset = (roots 511 true).toFinset := by decide +kernel
  exact eq ▸ solved511_14 0 (by decide +kernel)
def past511 : List (Nat × Nat) := (511,15)::past509
theorem pastOK511 : AugKnown past511 := augExtend extra511 pastOK509

-- Evaluate the posted indexed program on every row, including its constant pin
-- and its default reads, then apply the fifteen-gate bound for the suffix.
abbrev Pin := Fin 26
abbrev Op := Fin 3 × Pin × Pin
abbrev Signal := Wire Row
def falseWire : Signal := fun _ => false

def wireRead (ws : List Signal) (i : Pin) : Signal :=
  if i.val = 25 then fun _ => true else ws.getD i.val falseWire

def boolRead (ws : List Bool) (i : Pin) :=
  if i.val = 25 then true else ws.getD i.val false

def boolStep (ws : List Bool) (g : Op) :=
  ws ++ [if g.1.val = 0 then boolRead ws g.2.1 && boolRead ws g.2.2
    else if g.1.val = 1 then boolRead ws g.2.1 || boolRead ws g.2.2
    else !(boolRead ws g.2.1)]

def wireValue (ws : List Signal) (g : Op) :=
  if g.1.val = 0 then combine false (wireRead ws g.2.1) (wireRead ws g.2.2)
  else if g.1.val = 1 then combine true (wireRead ws g.2.1) (wireRead ws g.2.2)
  else inv (wireRead ws g.2.1)

def wireStep (ws : List Signal) (g : Op) := ws ++ [wireValue ws g]

def onRow (r : Row) (s : Signal) := s r

theorem readMap (r : Row) (ws : List Signal) (i : Nat) :
    (ws.map (onRow r)).getD i false = (ws.getD i falseWire) r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem readPins (r : Row) (ws : List Signal) (i : Pin) :
    boolRead (ws.map (onRow r)) i = wireRead ws i r := by
  by_cases h : i.val=25
  · simp only [boolRead,wireRead,h,ite_true]
  · simpa only [boolRead,wireRead,h,ite_false] using readMap r ws i.val

theorem evalStep (r : Row) (ws : List Signal) (g : Op) :
    (wireStep ws g).map (onRow r) = boolStep (ws.map (onRow r)) g := by
  simp only [wireStep,boolStep,List.map_append,List.map_singleton,readPins]
  by_cases a : g.1.val=0 <;> by_cases b : g.1.val=1 <;>
    simp [wireValue,a,b,onRow,combine,inv]

theorem evalTail (r : Row) (gs : List Op) (ws : List Signal) :
    (gs.foldl wireStep ws).map (onRow r) = gs.foldl boolStep (ws.map (onRow r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,List.foldl_cons,ih,evalStep]

theorem suppliedRead {bank ws : List Signal} (hs : supply bank ws) (i : Nat) :
    Available bank (ws.getD i falseWire) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inr ⟨false,rfl⟩
  | some a => exact hs a (List.mem_of_getElem? h)

theorem suppliedPin {bank ws : List Signal} (hs : supply bank ws) (i : Pin) :
    Available bank (wireRead ws i) := by
  unfold wireRead
  split
  · exact Or.inr ⟨true,rfl⟩
  · exact suppliedRead hs _

theorem stepReach {base bank ws : List Signal} {p : Nat}
    (hr : Reach base p bank) (hs : supply bank ws) (g : Op) :
    Reach base (p+1) (wireValue ws g::bank) := by
  unfold wireValue
  split
  · exact Reach.two false hr (suppliedPin hs _) (suppliedPin hs _)
  split
  · exact Reach.two true hr (suppliedPin hs _) (suppliedPin hs _)
  · exact Reach.one hr (suppliedPin hs _)

theorem tailReach {base bank ws : List Signal} {p} (gs : List Op)
    (hr : Reach base p bank) (hs : supply bank ws) :
    ∃ last, Reach base (p+gs.length) last ∧ supply last (gs.foldl wireStep ws) := by
  induction gs generalizing bank ws p with
  | nil => exact ⟨bank,hr,hs⟩
  | cons g gs ih =>
    have next : supply (wireValue ws g::bank) (wireStep ws g) := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact available_cons _ (hs a h)
      · exact Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
    obtain ⟨last,run,stock⟩ := ih (stepReach hr hs g) next
    exact ⟨last,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run,stock⟩

def varsAt (r : Row) (i : Fin 9) := r.val.testBit i.val
def wanted (r : Row) :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
    varsAt r (Fin.ofNat 9 (e/10)) && varsAt r (Fin.ofNat 9 (e % 10))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rowBase : ∀ r : Row, (roots 511 true).map (bit r) =
    List.ofFn (varsAt r) ++ [varsAt r 0 || varsAt r 4] := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rowGoal : ∀ r : Row, bit r (graphGoal 511) = wanted r := by decide +kernel

theorem rawProgramBound (lower : Lower (roots 511 true) (graphGoal 511) 15)
    (a b out : Pin) (tail : List Op) (sz : tail.length ≤ 13) :
    ∃ n < 512, let x : Fin 9 → Bool := fun i => n.testBit i.val
      (((1,a,b)::tail).foldl boolStep (List.ofFn x ++ [x 0 || x 4])).getD out.val false ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e =>
        x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10))) := by
  by_contra! good
  let gs : List Op := (1,a,b)::tail
  let base := (roots 511 true).map observe
  let outSig := (gs.foldl wireStep base).getD out.val falseWire
  have eq : outSig = observe (graphGoal 511) := by
    funext r
    change ((gs.foldl wireStep base).getD out.val falseWire) r = bit r (graphGoal 511)
    rw [←readMap,evalTail,rowGoal]
    have raw : base.map (onRow r) = (roots 511 true).map (bit r) := by
      rw [show base=(roots 511 true).map observe from rfl,List.map_map]
      rfl
    rw [raw,rowBase]
    exact not_ne_iff.mp (good r.val r.isLt)
  obtain ⟨last,hr,hs⟩ := tailReach gs (base:=base) Reach.start
    (show supply base base from fun _ h => Or.inl h)
  have hit : Available last outSig := suppliedRead hs _
  have bound := lower _ last hr (eq ▸ hit)
  change 15 ≤ 0+(tail.length+1) at bound
  omega

end PEqualNP.Outside.L_meta_3079

theorem PEqualNP.Outside.L_meta_3079 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b out tail size _ _ _ _
  exact PEqualNP.Outside.L_meta_3079.rawProgramBound PEqualNP.Outside.L_meta_3079.extra511 a b out tail size
