import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2335

-- The wire table and gate simplifier follow L-meta-2169.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]


private lemma elimPass_append (n : ℕ) (A B : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass n (A ++ B) acc = elimPass n B (elimPass n A acc) := by
  simp [elimPass, List.foldl_append]

private lemma elimPass_stats (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_preserves (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i : ℕ) (hi : i < acc.1.length) :
    (elimPass n gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def touches (S : Finset ℕ) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (i ∈ S)

private lemma touches_iff (S : Finset ℕ) (g : Gate) :
    touches S g = true ↔ ∃ i ∈ g.inputs, i ∈ S := by
  simp [touches, List.any_eq_true]

private lemma elimStep_le (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
  simp only [elimStep, List.length_append, Nat.add_le_add_iff_left]
  exact toList_opt_len_le _

private lemma elimStep_drop (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hg : NOkGate g) {i : ℕ} (hi : i ∈ g.inputs) {b : Bool}
    (hb : acc.1.getD i (Sum.inl false) = Sum.inl b) :
    (elimStep n acc g).2 = acc.2 := by
  let ins := g.inputs.map fun j => acc.1.getD j (Sum.inl false)
  have hn : (simplifyGate g.op (n + acc.2.length) ins).1 = none :=
    simplifyGate_none_of_const _ _ _ hg.1.1 (by simpa [ins] using hg.1.2)
      (fun h => by simpa [ins] using hg.2 h) ⟨b, List.mem_map.mpr ⟨i, hi, hb⟩⟩
  change acc.2 ++ (simplifyGate _ _ ins).1.toList = acc.2
  simp [hn]

private lemma elimPass_count (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ gs, NOkGate g) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < acc.1.length ∧ ∃ b, acc.1.getD i (Sum.inl false) = Sum.inl b) :
    (elimPass n gs acc).2.length + gs.countP (touches S) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    have ht := ih (elimStep n acc g) (fun a hm => h a (List.mem_cons_of_mem _ hm)) (by
      intro i hi
      obtain ⟨hlt, b, hb⟩ := hS i hi
      exact ⟨by simp [elimStep]; omega, b, (getD_snoc_lt _ _ _ _ hlt).trans hb⟩)
    rw [elimPass_cons, List.countP_cons, List.length_cons]
    cases he : touches S g with
    | false =>
      have hb := elimStep_le n acc g
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      obtain ⟨i, hi, hSi⟩ := (touches_iff S g).mp he
      obtain ⟨_, b, hb⟩ := hS i hSi
      rw [elimStep_drop n acc g (h g List.mem_cons_self) hi hb] at ht
      simp only [↓reduceIte]
      omega

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private lemma wiresFrom_noread (gs : List Gate) (w z : List Bool) (k : ℕ)
    (hgs : ∀ g ∈ gs, k ∉ g.inputs)
    (hlen : w.length = z.length)
    (hget : ∀ i, i ≠ k → w.getD i false = z.getD i false) :
    ∀ i, i ≠ k → (wiresFrom gs w).getD i false = (wiresFrom gs z).getD i false := by
  induction gs generalizing w z with
  | nil => exact hget
  | cons g gs ih =>
    have he : gateValue g w = gateValue g z := by
      unfold gateValue
      congr 1
      exact List.map_congr_left fun i hi => hget i (fun h => hgs g List.mem_cons_self (h ▸ hi))
    intro i hi
    rw [wiresFrom_cons, wiresFrom_cons]
    change (wiresFrom gs (w ++ [gateValue g w])).getD i false =
      (wiresFrom gs (z ++ [gateValue g z])).getD i false
    apply ih _ _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) (by simp [hlen]) _ i hi
    intro j hj
    by_cases h : j = w.length
    · rw [getD_snoc_eq _ _ _ _ h, getD_snoc_eq _ _ _ _ (h.trans hlen), he]
    · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (ne_of_ne_of_eq h hlen), hget j hj]

private def skip (k i : ℕ) : ℕ := if k < i then i - 1 else i

private def skipGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (skip k)⟩

private lemma wiresFrom_skip (gs : List Gate) (w z : List Bool) (k : ℕ)
    (hgs : ∀ g ∈ gs, k ∉ g.inputs)
    (hk : k < w.length) (hlen : w.length = z.length + 1)
    (hget : ∀ i, i ≠ k → w.getD i false = z.getD (skip k i) false) :
    ∀ i, i ≠ k → (wiresFrom gs w).getD i false =
      (wiresFrom (gs.map (skipGate k)) z).getD (skip k i) false := by
  induction gs generalizing w z with
  | nil => exact hget
  | cons g gs ih =>
    have he : gateValue g w = gateValue (skipGate k g) z := by
      simp only [gateValue, skipGate, List.map_map]
      congr 1
      exact List.map_congr_left fun i hi => hget i (fun h => hgs g List.mem_cons_self (h ▸ hi))
    intro i hi
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    change (wiresFrom gs (w ++ [gateValue g w])).getD i false =
      (wiresFrom (gs.map (skipGate k)) (z ++ [gateValue (skipGate k g) z])).getD (skip k i) false
    apply ih _ _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
      (by simp; omega) (by simp; omega) _ i hi
    intro j hj
    have hshift : skip k j = z.length ↔ j = w.length := by
      unfold skip
      split <;> omega
    by_cases h : j = w.length
    · rw [getD_snoc_eq _ _ _ _ h, getD_snoc_eq _ _ _ _ (hshift.mpr h), he]
    · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (mt hshift.mp h), hget j hj]

-- A gate with no later reader can be removed by shifting the later wire indices.
private lemma mustRead {n : ℕ} {A B : List Gate} {g : Gate} {o : ℕ}
    (hmin : IsMinimalCircuit n ⟨A ++ g :: B, o⟩) (ho : o ≠ n + A.length) :
    ∃ a ∈ B, n + A.length ∈ a.inputs := by
  classical
  by_contra! hnone
  let k := n + A.length
  let D : Circuit := ⟨A ++ B.map (skipGate k), skip k o⟩
  have hD : FanInTwo D := by
    intro a ha
    change a ∈ A ++ B.map (skipGate k) at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hmin.1 a (List.mem_append_left _ ha)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      simpa [skipGate] using hmin.1 b (List.mem_append_right _ (List.mem_cons_of_mem _ hb))
  have he : circuitFun n D = circuitFun n ⟨A ++ g :: B, o⟩ := by
    funext x
    let z := wiresFrom A (List.ofFn x)
    have hz : z.length = k := by simp [z, k, wiresFrom_length]
    let w := z ++ [gateValue g z]
    have hw : w.length = z.length + 1 := by simp [w]
    have hv : ∀ i, i ≠ k → w.getD i false = z.getD (skip k i) false := by
      intro i hi
      rw [show w.getD i false = z.getD i false from getD_snoc_ne _ _ _ _ (by omega)]
      by_cases h : k < i
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [skip, h]; omega)]
      · simp [skip, h]
    change (wiresFrom (A ++ B.map (skipGate k)) (List.ofFn x)).getD (skip k o) false =
      (wiresFrom (A ++ g :: B) (List.ofFn x)).getD o false
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons]
    exact (wiresFrom_skip B w z k hnone (by omega) hw hv o ho).symm
  have hs := hmin.2 D hD he
  simp [D, Circuit.size] at hs

private def liftInput (x : Fin 8 → Bool) : Fin 9 → Bool :=
  Fin.insertNth (6 : Fin 9) false x

private lemma liftInput_project (x : Fin 9 → Bool) (hx : x 6 = false) :
    liftInput (fun i => x ((6 : Fin 9).succAbove i)) = x := by
  unfold liftInput
  rw [← hx]
  exact Fin.insertNth_self_removeNth 6 x

private def fixedInput (x : Fin 8 → Bool) : List Bool :=
  [x 0, x 1, x 2, x 3, x 4, x 5, false, x 6, x 7]

private lemma fixed_eq (x : Fin 8 → Bool) : List.ofFn (liftInput x) = fixedInput x := by
  apply List.ext_getElem
  · simp [fixedInput]
  · intro i hi _
    have h : i < 9 := by simpa using hi
    interval_cases i <;> rfl

private def initial : List (Bool ⊕ ℕ) × List Gate :=
  ([Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inl false,
    Sum.inr 6, Sum.inr 7, Sum.inl false], [])

private lemma first_inv (x : Fin 8 → Bool) :
    ElimInv 8 (List.ofFn x) (fixedInput x ++ [false]) initial := by
  refine ⟨List.length_ofFn, rfl, ?_⟩
  intro i
  by_cases hi : i < 10
  · interval_cases i <;>
      simp [initial, fixedInput, statValid, statVal, wiresFrom_nil, List.getD]
  · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp [fixedInput]; omega)]
    exact ⟨trivial, rfl⟩

private def probe0 (i : Fin 9) : Bool := decide (i = 8)
private def probe6 (i : Fin 9) : Bool := decide (i = 6 ∨ i = 8)

private lemma needsSix (f : Gate) (gs : List Gate) (o : ℕ) (ho : o ≠ 6)
    (hf : ∀ x : Fin 9 → Bool, gateValue f (List.ofFn x) = (x 0 && x 6))
    (hne : circuitFun 9 ⟨f :: gs, o⟩ probe0 ≠ circuitFun 9 ⟨f :: gs, o⟩ probe6) :
    ∃ g ∈ gs, 6 ∈ g.inputs := by
  by_contra! hnone
  apply hne
  have hf0 : gateValue f (List.ofFn probe0) = false := by rw [hf]; rfl
  have hf6 : gateValue f (List.ofFn probe6) = false := by rw [hf]; rfl
  change (wiresFrom (f :: gs) (List.ofFn probe0)).getD o false =
    (wiresFrom (f :: gs) (List.ofFn probe6)).getD o false
  rw [wiresFrom_cons, wiresFrom_cons]
  change (wiresFrom gs (List.ofFn probe0 ++ [gateValue f (List.ofFn probe0)])).getD o false =
    (wiresFrom gs (List.ofFn probe6 ++ [gateValue f (List.ofFn probe6)])).getD o false
  rw [hf0, hf6]
  apply wiresFrom_noread _ _ _ 6 hnone (by simp) _ o ho
  intro i hi
  by_cases h : i < 10
  · interval_cases i <;> first | exact (hi rfl).elim | rfl
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma onlySixNine {ins : List ℕ} (hl : ins.length ≤ 2)
    (h6 : 6 ∈ ins) (h9 : 9 ∈ ins) :
    ∀ i ∈ ins, i = 6 ∨ i = 9 := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all
  all_goals aesop

private lemma simplify_constant (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hins : ∀ s ∈ ins, s = Sum.inl false) :
    ∃ b, (simplifyGate op m ins).2 = Sum.inl b := by
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [simplifyGate, simpAnd, simpOr, simpNot]

private lemma remove (f : Gate) (gs : List Gate) (o : ℕ)
    (hmin : IsMinimalCircuit 9 ⟨f :: gs, o⟩)
    (hok : ∀ g ∈ gs, NOkGate g)
    (hf : ∀ x : Fin 9 → Bool, gateValue f (List.ofFn x) = (x 0 && x 6))
    (hne : circuitFun 9 ⟨f :: gs, o⟩ probe0 ≠ circuitFun 9 ⟨f :: gs, o⟩ probe6)
    (hvar : ∃ y z : Fin 8 → Bool,
      circuitFun 9 ⟨f :: gs, o⟩ (liftInput y) ≠ circuitFun 9 ⟨f :: gs, o⟩ (liftInput z)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ (⟨f :: gs, o⟩ : Circuit).size ∧
      ∀ x : Fin 8 → Bool, circuitFun 8 D x = circuitFun 9 ⟨f :: gs, o⟩ (liftInput x) := by
  let final := elimPass 8 gs initial
  have inv (x : Fin 8 → Bool) :
      ElimInv 8 (List.ofFn x) (wiresFrom (f :: gs) (List.ofFn (liftInput x))) final := by
    rw [wiresFrom_cons]
    change ElimInv 8 (List.ofFn x)
      (wiresFrom gs (List.ofFn (liftInput x) ++ [gateValue f (List.ofFn (liftInput x))])) final
    rw [hf, show liftInput x 6 = false from Fin.insertNth_apply_same _ _ _,
      Bool.and_false, fixed_eq]
    exact elimInv_pass _ _ _ _ _ (fun g hg => (hok g hg).1) (first_inv x)
  have heval (x : Fin 8 → Bool) :
      statVal (wiresFrom final.2 (List.ofFn x)) (final.1.getD o (Sum.inl false)) =
        circuitFun 9 ⟨f :: gs, o⟩ (liftInput x) := ((inv x).2.2 o).2
  have hnotconst {i : ℕ} {b : Bool} (hb : final.1.getD i (Sum.inl false) = Sum.inl b) :
      o ≠ i := by
    rintro rfl
    obtain ⟨y, z, hyz⟩ := hvar
    have hy := heval y
    have hz := heval z
    rw [hb] at hy hz
    exact hyz (hy.symm.trans hz)
  have hknown (ls : List Gate) (i : ℕ) (hi : i = 6 ∨ i = 9) :
      i < (elimPass 8 ls initial).1.length ∧
        (elimPass 8 ls initial).1.getD i (Sum.inl false) = Sum.inl false := by
    rcases hi with rfl | rfl
    all_goals
      rw [elimPass_preserves _ _ _ _ (by decide)]
      exact ⟨by rw [elimPass_stats]; change _ < 10 + _; omega, rfl⟩
  have h6 := needsSix f gs o (hnotconst (hknown gs 6 (Or.inl rfl)).2) hf hne
  obtain ⟨g, hg, h9⟩ := mustRead (A := []) (B := gs) (g := f) (o := o) hmin
    (hnotconst (hknown gs 9 (Or.inr rfl)).2)
  change 9 ∈ g.inputs at h9
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hg
  let prefixAcc := elimPass 8 A initial
  let middleAcc := elimStep 8 prefixAcc g
  let S : Finset ℕ := {6, 9}
  have hS (i : ℕ) : i ∈ S ↔ i = 6 ∨ i = 9 := by simp [S]
  have hA : ∀ a ∈ A, NOkGate a := fun a ha => hok a (List.mem_append_left _ ha)
  have hB : ∀ a ∈ B, NOkGate a := fun a ha =>
    hok a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  have hgok := hok g (List.mem_append_right A List.mem_cons_self)
  have hmid : middleAcc.2.length = prefixAcc.2.length := by
    exact congrArg List.length (elimStep_drop 8 prefixAcc g hgok h9 (hknown A 9 (Or.inr rfl)).2)
  have hAcount := elimPass_count 8 A initial hA S (by
    intro i hi
    obtain ⟨hlt, heq⟩ := hknown [] i ((hS i).mp hi)
    exact ⟨hlt, false, heq⟩)
  change prefixAcc.2.length + A.countP (touches S) ≤ 0 + A.length at hAcount
  have hBcount := elimPass_count 8 B middleAcc hB S (by
    intro i hi
    obtain ⟨hlt, heq⟩ := hknown A i ((hS i).mp hi)
    change i < prefixAcc.1.length at hlt
    exact ⟨by change i < (prefixAcc.1 ++ [_]).length; simp; omega, false,
      (getD_snoc_lt _ _ _ _ hlt).trans heq⟩)
  have hfinal : final = elimPass 8 B middleAcc := by
    exact (elimPass_append 8 A (g :: B) initial).trans (elimPass_cons 8 g B prefixAcc)
  have hsize : final.2.length + 3 ≤ (⟨f :: (A ++ g :: B), o⟩ : Circuit).size := by
    rw [hfinal]
    simp only [Circuit.size, List.length_cons, List.length_append]
    by_cases hmore : 0 < A.countP (touches S) + B.countP (touches S)
    · omega
    · -- The only reader of wires 6 and 9 now produces a constant.
      have hnoneA : ∀ a ∈ A, ¬ touches S a := List.countP_eq_zero.mp (by omega)
      have hnoneB : ∀ a ∈ B, ¬ touches S a := List.countP_eq_zero.mp (by omega)
      have hg6 : 6 ∈ g.inputs := by
        obtain ⟨a, ha, ha6⟩ := h6
        have htouch : touches S a := (touches_iff S a).mpr ⟨6, ha6, (hS 6).mpr (Or.inl rfl)⟩
        rcases List.mem_append.mp ha with ha | ha
        · exact (hnoneA a ha htouch).elim
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact ha6
          · exact (hnoneB a ha htouch).elim
      let k := prefixAcc.1.length
      have hk : k = 9 + (f :: A).length := by
        simp [k, prefixAcc, elimPass_stats, initial]
        omega
      have hkg : ∃ b, middleAcc.1.getD k (Sum.inl false) = Sum.inl b := by
        let ins := g.inputs.map fun j => prefixAcc.1.getD j (Sum.inl false)
        have hall : ∀ s ∈ ins, s = Sum.inl false := by
          intro s hs
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
          exact (hknown A i (onlySixNine hgok.1.2 hg6 h9 i hi)).2
        obtain ⟨b, hb⟩ := simplify_constant g.op (8 + prefixAcc.2.length) ins
          hgok.1.1 (by simpa [ins] using hgok.1.2) hall
        exact ⟨b, (getD_snoc_eq _ _ _ _ rfl).trans hb⟩
      obtain ⟨b, hb⟩ := hkg
      have hlt : k < middleAcc.1.length := by simp [k, middleAcc, elimStep]
      have hkout : o ≠ k := hnotconst (by
        rw [hfinal, elimPass_preserves _ _ _ _ hlt]
        exact hb)
      obtain ⟨a, ha, hak⟩ := mustRead (A := f :: A) (B := B) (g := g) (o := o) hmin
        (by rwa [hk] at hkout)
      rw [← hk] at hak
      have hlast := elimPass_count 8 B middleAcc hB {k} (by
        intro i hi
        obtain rfl : i = k := Finset.mem_singleton.mp hi
        exact ⟨hlt, b, hb⟩)
      have hpos : 0 < B.countP (touches {k}) := List.countP_pos_iff.mpr
        ⟨a, ha, (touches_iff {k} a).mpr ⟨k, hak, Finset.mem_singleton_self k⟩⟩
      omega
  cases h : final.1.getD o (Sum.inl false) with
  | inl b => exact (hnotconst h rfl).elim
  | inr i =>
    refine ⟨⟨final.2, i⟩, elimPass_ok 8 _ _ (by simp [initial]), hsize, ?_⟩
    intro x
    have hx := heval x
    rw [h] at hx
    exact hx

end PEqualNP.Outside.L_meta_2335

theorem PEqualNP.Outside.L_meta_2335 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)))) → ((PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = (8 : Fin (9 : ℕ)))) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = (6 : Fin (9 : ℕ)) ∨ x4 = (8 : Fin (9 : ℕ)))) → ((PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x5 : Fin (9 : ℕ)) => Bool.false) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = (1 : Fin (9 : ℕ)) ∨ x5 = (2 : Fin (9 : ℕ)))) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size + (3 : ℕ) ≤ x1.size ∧ ∀ (x7 : Fin (9 : ℕ) → Bool), x7 (6 : Fin (9 : ℕ)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x6 fun (x9 : Fin (8 : ℕ)) => x7 (Fin.succAbove (6 : Fin (9 : ℕ)) x9)) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x7 := by
  intro C hmin hfirst hdiff hvar
  open PEqualNP.Outside.L_meta_2335 in
  exact by
    let N : Circuit := ⟨C.gates.map normGate, C.output⟩
    have hsize : N.size = C.size := List.length_map _
    have hw (x : List Bool) : N.wires x = C.wires x := wiresFrom_norm C.gates x
    have heval : circuitFun 9 N = circuitFun 9 C := by
      funext x
      exact congrArg (fun w => w.getD C.output false) (hw (List.ofFn x))
    have hnorm : ∀ g ∈ N.gates, NOkGate g := by
      intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact normGate_nok a (hmin.1 a ha)
    have hminN : IsMinimalCircuit 9 N := by
      refine ⟨fun g hg => (hnorm g hg).1, ?_⟩
      rw [hsize]
      intro D hD he
      exact hmin.2 D hD (he.trans heval)
    let o := N.output
    cases hgs : N.gates with
    | nil =>
      have h := hfirst (fun _ => true)
      rw [← hw] at h
      change (wiresFrom N.gates (List.ofFn fun _ : Fin 9 => true)).getD 9 false =
        true at h
      rw [hgs, wiresFrom_nil, List.getD_eq_default _ _ (by simp)] at h
      contradiction
    | cons f gs =>
      have hshape : N = ⟨f :: gs, o⟩ := by
        rw [← hgs]
      have hf (x : Fin 9 → Bool) : gateValue f (List.ofFn x) = (x 0 && x 6) := by
        have h := hfirst x
        rw [← hw, hshape] at h
        change (wiresFrom (f :: gs) (List.ofFn x)).getD 9 false = _ at h
        rw [wiresFrom_cons, wiresFrom_getD_lt _ _ _ (by simp),
          getD_snoc_eq _ _ _ _ (by simp)] at h
        exact h
      have hdiffN : circuitFun 9 N probe0 ≠ circuitFun 9 N probe6 := by
        rw [heval]
        exact hdiff
      have hvarN : ∃ y z : Fin 8 → Bool,
          circuitFun 9 N (liftInput y) ≠ circuitFun 9 N (liftInput z) := by
        let y : Fin 9 → Bool := fun _ => false
        let z : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
        refine ⟨fun i => y ((6 : Fin 9).succAbove i), fun i => z ((6 : Fin 9).succAbove i), ?_⟩
        rw [liftInput_project y rfl, liftInput_project z (by decide), heval]
        exact hvar
      rw [hshape] at hminN hdiffN hvarN hnorm hsize heval
      obtain ⟨D, hD, hs, he⟩ := remove f gs o hminN
        (fun g hg => hnorm g (List.mem_cons_of_mem _ hg)) hf hdiffN hvarN
      refine ⟨D, hD, hs.trans_eq hsize, ?_⟩
      intro x hx
      rw [he, liftInput_project x hx, heval]
