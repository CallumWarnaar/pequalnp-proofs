import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4119

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht, List.length_append, hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

def up (k i : ℕ) : ℕ := if i < k then i else i + 1

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
  unfold up eraseRedirect
  split_ifs <;> omega

theorem sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
    (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
    V.length = U.length + 1 →
    ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
      ∀ g ∈ rest, n + m ∉ g.inputs) →
    ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
      (rest.foldl step V).getD (up (n + m) i) false
  | [], U, V, hrel, _, _, _ => by simpa using hrel
  | g :: rest, U, V, hrel, hk, hlen, hS => by
    have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hS with ⟨hS, -⟩ | hS
        · simpa [eraseRedirect] using hS
        · exact absurd hr (hS g (List.mem_cons_self ..))
      · rw [hrel, up_redir n m p r hrk]
    set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
    have hU : step U (ren n m p g) = U ++ [a] := by
      simp only [step, ren, List.map_map]
      congr 3
      exact List.map_congr_left fun r hr => hread r hr
    have hV : step V g = V ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, hU, hV]
    apply sim n m p rest
    · intro i
      rcases lt_trichotomy i U.length with hi | rfl | hi
      · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
      · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
        rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
        simp
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
    · simp; omega
    · simp; omega
    · rcases hS with ⟨hS, hp⟩ | hS
      · left
        refine ⟨?_, ?_⟩
        · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
          rcases hp with hp | hp
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
          · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
            rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
            exact hS
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; simp at hp ⊢; omega
      · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
    (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
    (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval y = C.eval y := by
  obtain ⟨hg, ho⟩ := erase_gates n C m p hm
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set A := (C.gates.take m).foldl step y with hA
  have hAl : A.length = n + m := by
    rw [hA, fold_length, hy, List.length_take]; omega
  set rest := C.gates.drop (m + 1) with hrest
  have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
  have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
    rw [wires_eq, hg, List.foldl_append]
  have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
  have hWl : (C.wires y).length = n + C.gates.length := by
    rw [wires_eq, fold_length, hy]
  have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
    intro i hi
    rw [hW, fold_getD_lt _ _ _ (by omega)]
  have hsim := sim n m p rest A (step A C.gates[m]) (by
      intro i
      by_cases hi : i < n + m
      · simp only [up, if_pos hi, step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [up, if_neg hi]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
    (by omega) hVl (by
      rcases hc with hc | ⟨-, hc⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hstable _ (by omega)]
          rcases hp with hp | hp
          · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
          · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; omega
      · exact Or.inr hc)
  unfold Circuit.eval
  rw [ho, hW', hsim, ← hW]
  by_cases hout : C.output = n + m
  · rcases hc with hc | ⟨hc, -⟩
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout]
      rcases hp with hp | hp
      · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
        rw [hu]; exact hc.symm
      · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
        rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · exact absurd hout hc
  · rw [up_redir n m p _ hout]

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  unfold Circuit.size
  rw [(erase_gates n C m p hm).1]
  simp
  omega

theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (eraseGate n C m p) := by
  intro g hg
  rw [(erase_gates n C m p hm).1, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [ren] using h2⟩

def sub (a b B i : ℕ) : ℕ := if i = a ∨ i = b then B else i

def fixC (a b : ℕ) (C : Circuit) (B : ℕ) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (sub a b B)⟩), sub a b B C.output⟩

def Inv (a b B : ℕ) (U V : List Bool) (k : ℕ) : Prop :=
  U.length = V.length ∧ (∀ i, i ≠ a → i ≠ b → U.getD i false = V.getD i false) ∧
    V.getD a false = false ∧ V.getD b false = false ∧ a < V.length ∧ b < V.length ∧
    V.length + k ≤ B ∧ B ≠ a ∧ B ≠ b

theorem inv_read (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V k) (r : ℕ) :
    U.getD (sub a b B r) false = V.getD r false := by
  obtain ⟨-, hrel, hVa, hVb, -, -, hB, hBa, hBb⟩ := h
  unfold sub
  split_ifs with hr
  · rw [hrel B hBa hBb, getD_ge _ _ (by omega)]
    rcases hr with rfl | rfl
    · exact hVa.symm
    · exact hVb.symm
  · push_neg at hr
    exact hrel r hr.1 hr.2

theorem inv_snoc (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V (k + 1)) (v : Bool) :
    Inv a b B (U ++ [v]) (V ++ [v]) k := by
  obtain ⟨hl, hrel, hVa, hVb, ha, hb, hB, hBa, hBb⟩ := h
  refine ⟨by simp [hl], fun i hia hib => ?_, ?_, ?_, by simp; omega, by simp; omega,
    by simp; omega, hBa, hBb⟩
  · rcases lt_trichotomy i V.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi, hrel i hia hib]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl, hl]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
  · rw [List.getD_append _ _ _ _ ha]; exact hVa
  · rw [List.getD_append _ _ _ _ hb]; exact hVb

theorem fix_fold (a b B : ℕ) : ∀ (gs : List Gate) (U V : List Bool), Inv a b B U V gs.length →
    Inv a b B ((gs.map fun g => (⟨g.op, g.inputs.map (sub a b B)⟩ : Gate)).foldl step U)
      (gs.foldl step V) 0
  | [], U, V, h => by simpa using h
  | g :: gs, U, V, h => by
    set v := g.op.eval (g.inputs.map fun i => V.getD i false)
    have hU : step U ⟨g.op, g.inputs.map (sub a b B)⟩ = U ++ [v] := by
      simp only [step, List.map_map]
      congr 3
      exact List.map_congr_left fun r _ => inv_read a b B U V _ h r
    simp only [List.map_cons, List.foldl_cons, hU]
    exact fix_fold a b B gs _ _ (inv_snoc a b B U V gs.length h v)

theorem fix_eval (n : ℕ) (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
    (fixC a b C (n + C.gates.length)).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
  set y := Function.update (Function.update x a false) b false
  have hinit : Inv a b (n + C.gates.length) (List.ofFn x) (List.ofFn y) C.gates.length := by
    refine ⟨by simp, fun i hia hib => ?_, ?_, ?_, by simp, by simp, by simp, by omega, by omega⟩
    · by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn, List.getElem_ofFn]
        have h1 : (⟨i, hi⟩ : Fin n) ≠ b := fun h => hib (by rw [← h])
        have h2 : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (by rw [← h])
        simp only [y, Function.update_of_ne h1, Function.update_of_ne h2]
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      by_cases hab : a = b
      · simp [y, hab]
      · simp [y, Function.update_of_ne hab]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp [y]
  have := fix_fold a b (n + C.gates.length) C.gates _ _ hinit
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact inv_read a b _ _ _ _ this C.output

theorem fix_size (a b B : ℕ) (C : Circuit) : (fixC a b C B).size = C.size := by
  simp [fixC, Circuit.size]

theorem fix_fanin (a b B : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (fixC a b C B) := by
  intro g hg
  simp only [fixC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hC g' hg'
  exact ⟨h1, by simpa using h2⟩

def NotUnary (C : Circuit) : Prop := ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1

theorem fix_notu (a b B : ℕ) (C : Circuit) (hC : NotUnary C) : NotUnary (fixC a b C B) := by
  intro g hg hop
  simp only [fixC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  simpa using hC g' hg' hop

theorem erase_notu (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hC : NotUnary C) : NotUnary (eraseGate n C m p) := by
  intro g hg hop
  rw [(erase_gates n C m p hm).1, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg) hop
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [ren] using hC g' (List.mem_of_mem_drop hg') hop

def nrm (g : Gate) : Gate :=
  match g with
  | ⟨GateOp.not, l⟩ => ⟨GateOp.not, l.take 1⟩
  | g => g

def normC (C : Circuit) : Circuit := ⟨C.gates.map nrm, C.output⟩

theorem nrm_cases (g : Gate) : (g.op = GateOp.not ∧ nrm g = ⟨GateOp.not, g.inputs.take 1⟩) ∨
    (g.op ≠ GateOp.not ∧ nrm g = g) := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [nrm]

theorem step_nrm (w : List Bool) (g : Gate) : step w (nrm g) = step w g := by
  rcases nrm_cases g with ⟨h, h2⟩ | ⟨_, h2⟩
  · rw [h2]
    simp only [step, h, GateOp.eval]
    congr 2
    cases g.inputs with
    | nil => rfl
    | cons r rs => rfl
  · rw [h2]

theorem fold_nrm : ∀ (gs : List Gate) (w : List Bool), (gs.map nrm).foldl step w = gs.foldl step w
  | [], w => rfl
  | g :: gs, w => by
    simp only [List.map_cons, List.foldl_cons, step_nrm]
    exact fold_nrm gs _

theorem norm_eval (C : Circuit) (y : List Bool) : (normC C).eval y = C.eval y := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  simp only [normC, fold_nrm]

theorem norm_size (C : Circuit) : (normC C).size = C.size := by
  simp [normC, Circuit.size]

theorem norm_fanin (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (normC C) := by
  intro g hg
  simp only [normC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hC g' hg'
  rcases nrm_cases g' with ⟨h, h3⟩ | ⟨_, h3⟩
  · rw [h3]
    refine ⟨by simp, ?_⟩
    simp only [List.length_take]; omega
  · rw [h3]; exact ⟨h1, h2⟩

theorem norm_notu (C : Circuit) : NotUnary (normC C) := by
  intro g hg hop
  simp only [normC, List.mem_map] at hg
  obtain ⟨g', _, rfl⟩ := hg
  rcases nrm_cases g' with ⟨_, h3⟩ | ⟨h, h3⟩
  · rw [h3]; simp
  · rw [h3] at hop ⊢; exact absurd hop h

theorem wire_gate (n : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.wires y).getD (n + k) false = C.gates[k].op.eval (C.gates[k].inputs.map
      fun i => if i < n + k then (C.wires y).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  set A := (C.gates.take k).foldl step y with hA
  have hAl : A.length = n + k := by
    rw [hA, fold_length, hy, List.length_take]; omega
  have hW : C.wires y = (C.gates.drop (k + 1)).foldl step (step A C.gates[k]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hA' : ∀ i, (if i < n + k then (C.wires y).getD i false else false) = A.getD i false := by
    intro i
    split_ifs with hi
    · rw [hW, fold_getD_lt _ _ _ (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [getD_ge _ _ (by omega)]
  have hL : (C.wires y).getD (n + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => A.getD i false) := by
    rw [hW, fold_getD_lt _ _ _ (by simp [step]; omega), step,
      List.getD_append_right _ _ _ _ (by omega)]
    simp only [hAl, Nat.sub_self, List.getD_cons_zero]
  rw [hL]
  congr 1
  exact List.map_congr_left fun i _ => (hA' i).symm

theorem wires_len (n : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n) :
    (C.wires y).length = n + C.gates.length := by
  rw [wires_eq, fold_length, hy]

theorem wire_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  rw [wires_eq, fold_getD_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]

def W (C : Circuit) (y : List Bool) (i : ℕ) : Bool := (C.wires y).getD i false

def Erasable (n : ℕ) (C : Circuit) (m p : ℕ) : Prop :=
  m < C.gates.length ∧ (p < n + m ∨ n + C.gates.length ≤ p) ∧
    ((∀ x : Fin n → Bool, W C (List.ofFn x) (n + m) = W C (List.ofFn x) p) ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs))

theorem W_big (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    W C (List.ofFn x) i = false :=
  getD_ge _ _ (by rw [wires_len n C _ (by simp)]; omega)

theorem W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W C (List.ofFn x) (n + k) = C.gates[k].op.eval (C.gates[k].inputs.map
      fun i => if i < n + k then W C (List.ofFn x) i else false) :=
  wire_gate n C _ (by simp) k hk

theorem first_diff (n : ℕ) (C : Circuit) (a : Fin n) (x : Fin n → Bool)
    (hne : C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x a false)))
    (hout : C.output ≠ a.val) :
    ∃ j, j < C.gates.length ∧
      (∀ i, i < n + j → i ≠ a.val →
        W C (List.ofFn x) i = W C (List.ofFn (Function.update x a false)) i) ∧
      W C (List.ofFn x) (n + j) ≠ W C (List.ofFn (Function.update x a false)) (n + j) := by
  classical
  set x' := Function.update x a false
  have hin : ∀ i, i < n → i ≠ a.val → W C (List.ofFn x) i = W C (List.ofFn x') i := by
    intro i hi hia
    have h1 := wire_input n C x ⟨i, hi⟩
    have h2 := wire_input n C x' ⟨i, hi⟩
    have hne' : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (by rw [← h])
    unfold W
    rw [h1, h2]
    simp [x', Function.update_of_ne hne']
  have hex : ∃ j, j < C.gates.length ∧ W C (List.ofFn x) (n + j) ≠ W C (List.ofFn x') (n + j) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold Circuit.eval
    change W C (List.ofFn x) C.output = W C (List.ofFn x') C.output
    by_cases h1 : C.output < n
    · exact hin _ h1 hout
    · by_cases h2 : C.output < n + C.gates.length
      · have := hcon (C.output - n) (by omega)
        rwa [show n + (C.output - n) = C.output by omega] at this
      · rw [W_big n C x _ (by omega), W_big n C x' _ (by omega)]
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, fun i hi hia => ?_, hj.2⟩
  by_cases h1 : i < n
  · exact hin i h1 hia
  · have hlt : i - n < j := by omega
    have hmin := Nat.find_min hex hlt
    push_neg at hmin
    have := hmin (by omega)
    rwa [show n + (i - n) = i by omega] at this

theorem reads_a (n : ℕ) (C : Circuit) (a : Fin n) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length)
    (heq : ∀ i, i < n + j → i ≠ a.val →
        W C (List.ofFn x) i = W C (List.ofFn (Function.update x a false)) i)
    (hd : W C (List.ofFn x) (n + j) ≠ W C (List.ofFn (Function.update x a false)) (n + j)) :
    a.val ∈ C.gates[j].inputs := by
  by_contra hna
  apply hd
  rw [W_gate n C x j hj, W_gate n C _ j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hia : i ≠ a.val := fun h => hna (h ▸ hi)
  split_ifs with h
  · exact heq i h hia
  · rfl

theorem ops (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not) ∧
      C.gates[k].inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hC _ (List.getElem_mem hk)
  refine ⟨?_, h2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem list_two (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ r, l = [r]) ∨ ∃ r s, l = [r, s] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [r], _ => exact Or.inr (Or.inl ⟨r, rfl⟩)
  | [r, s], _ => exact Or.inr (Or.inr ⟨r, s, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

theorem pass_through (n : ℕ) (C : Circuit) (k r : ℕ) (hk : k < C.gates.length)
    (hval : ∀ x : Fin n → Bool, W C (List.ofFn x) (n + k) =
      (if r < n + k then W C (List.ofFn x) r else false)) :
    ∃ p, Erasable n C k p := by
  by_cases hr : r < n + k
  · refine ⟨r, hk, Or.inl hr, Or.inl fun x => ?_⟩
    rw [hval x, if_pos hr]
  · refine ⟨n + C.gates.length, hk, Or.inr le_rfl, Or.inl fun x => ?_⟩
    rw [hval x, if_neg hr, W_big n C x _ le_rfl]

theorem const_false (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hval : ∀ x : Fin n → Bool, W C (List.ofFn x) (n + k) = false) :
    ∃ p, Erasable n C k p :=
  ⟨n + C.gates.length, hk, Or.inr le_rfl, Or.inl fun x => by rw [hval x, W_big n C x _ le_rfl]⟩

theorem const_true (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hnu : NotUnary C) (j : ℕ) (hj : j < C.gates.length)
    (htrue : ∀ x : Fin n → Bool, W C (List.ofFn x) (n + j) = true)
    (y0 : Fin n → Bool) (hy0 : C.eval (List.ofFn y0) = false) :
    ∃ m p, Erasable n C m p := by
  classical
  let T := (Finset.range C.gates.length).filter
    (fun t => ∀ x : Fin n → Bool, W C (List.ofFn x) (n + t) = true)
  have hjT : j ∈ T := by simp [T, hj, htrue]
  have hne : T.Nonempty := ⟨j, hjT⟩
  set t := T.max' hne with ht
  have htT : t ∈ T := T.max'_mem hne
  have htL : t < C.gates.length := by simpa [T] using (Finset.mem_filter.mp htT).1
  have htv : ∀ x : Fin n → Bool, W C (List.ofFn x) (n + t) = true := (Finset.mem_filter.mp htT).2
  have hmax : ∀ s, s < C.gates.length → (∀ x : Fin n → Bool, W C (List.ofFn x) (n + s) = true) →
      s ≤ t := fun s hs hv => T.le_max' s (by simp [T, hs, hv])
  by_cases hlow : ∃ s, s < t ∧ s < C.gates.length ∧
      ∀ x : Fin n → Bool, W C (List.ofFn x) (n + s) = true
  · obtain ⟨s, hst, -, hsv⟩ := hlow
    exact ⟨t, n + s, htL, Or.inl (by omega), Or.inl fun x => by rw [htv x, hsv x]⟩
  push_neg at hlow
  have hout : C.output ≠ n + t := by
    intro h
    have := htv y0
    unfold W at this
    unfold Circuit.eval at hy0
    rw [h] at hy0
    rw [hy0] at this
    exact Bool.false_ne_true this
  by_cases hread : ∃ g ∈ C.gates.drop (t + 1), n + t ∈ g.inputs
  · obtain ⟨g, hg, hgr⟩ := hread
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
    rw [List.length_drop] at hi
    set k := t + 1 + i with hkdef
    have hk : k < C.gates.length := by omega
    have hgk : C.gates[k] = g := by
      rw [← hgi, List.getElem_drop]
    have htk : n + t < n + k := by omega
    obtain ⟨hop, hlen⟩ := ops C hC k hk
    have hval := fun x => W_gate n C x k hk
    rw [hgk] at hop hlen hval
    have hnotin : ¬ (∀ x : Fin n → Bool, W C (List.ofFn x) (n + k) = true) := by
      intro hv
      have := hmax k hk hv
      omega
    rcases list_two g.inputs hlen with h0 | ⟨r, h1⟩ | ⟨r, s, h2⟩
    · rw [h0] at hgr; simp at hgr
    · rw [h1] at hgr
      simp only [List.mem_singleton] at hgr
      subst hgr
      rcases hop with hop | hop | hop
      · exfalso; apply hnotin; intro x
        rw [hval x, h1, hop]; simp [GateOp.eval, htk, htv x]
      · exfalso; apply hnotin; intro x
        rw [hval x, h1, hop]; simp [GateOp.eval, htk, htv x]
      · exact ⟨k, const_false n C k hk fun x => by
          rw [hval x, h1, hop]; simp [GateOp.eval, htk, htv x]⟩
    · rw [h2] at hgr
      rcases hop with hop | hop | hop
      · by_cases hr : r = n + t
        · by_cases hs : s = n + t
          · exfalso; apply hnotin; intro x
            rw [hval x, h2, hop, hr, hs]; simp [GateOp.eval, htk, htv x]
          · obtain ⟨p, hp⟩ := pass_through n C k s hk fun x => by
              rw [hval x, h2, hop, hr]; simp [GateOp.eval, htk, htv x]
            exact ⟨k, p, hp⟩
        · have hs : s = n + t := by simp at hgr; omega
          obtain ⟨p, hp⟩ := pass_through n C k r hk fun x => by
            rw [hval x, h2, hop, hs]; simp [GateOp.eval, htk, htv x]
          exact ⟨k, p, hp⟩
      · exfalso; apply hnotin; intro x
        rw [hval x, h2, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id]
        simp at hgr
        rcases hgr with hgr | hgr <;> subst hgr <;> simp [htk, htv x]
      · have := hnu g (hgk ▸ List.getElem_mem hk) hop
        rw [h2] at this; simp at this
  · push_neg at hread
    exact ⟨t, n + C.gates.length, htL, Or.inr (by omega), Or.inr ⟨hout, hread⟩⟩

theorem erasable_fixed (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hnu : NotUnary C) (a : Fin n) (j : ℕ) (hj : j < C.gates.length)
    (ha : a.val ∈ C.gates[j].inputs) (y0 : Fin n → Bool)
    (hy0 : (fixC a a C (n + C.gates.length)).eval (List.ofFn y0) = false) :
    ∃ m p, Erasable n (fixC a a C (n + C.gates.length)) m p := by
  set B := n + C.gates.length
  set C1 := fixC a a C B with hC1
  have hlen : C1.gates.length = C.gates.length := by simp [C1, fixC]
  have hj1 : j < C1.gates.length := by omega
  have hg1 : C1.gates[j] = ⟨C.gates[j].op, C.gates[j].inputs.map (sub a a B)⟩ := by
    simp [C1, fixC]
  have hsubB : sub a a B a = B := by simp [sub]
  have hsubr : ∀ r, r ≠ a.val → sub a a B r = r := by
    intro r hr; simp [sub, hr]
  have hBj : ¬ (B < n + j) := by omega
  have hval := fun x => W_gate n C1 x j hj1
  rw [hg1] at hval
  obtain ⟨hop, hlen2⟩ := ops C hC j hj
  rcases list_two _ hlen2 with h0 | ⟨r, h1⟩ | ⟨r, s, h2⟩
  · rw [h0] at ha; simp at ha
  · rw [h1] at ha
    simp only [List.mem_singleton] at ha
    rcases hop with hop | hop | hop
    · exact ⟨j, const_false n C1 j hj1 fun x => by
        rw [hval x, h1, hop, ← ha]; simp [GateOp.eval, hsubB, hBj]⟩
    · exact ⟨j, const_false n C1 j hj1 fun x => by
        rw [hval x, h1, hop, ← ha]; simp [GateOp.eval, hsubB, hBj]⟩
    · exact const_true n C1 (fix_fanin _ _ _ C hC) (fix_notu _ _ _ C hnu) j hj1
        (fun x => by rw [hval x, h1, hop, ← ha]; simp [GateOp.eval, hsubB, hBj]) y0 hy0
  · rw [h2] at ha
    rcases hop with hop | hop | hop
    · exact ⟨j, const_false n C1 j hj1 fun x => by
        rw [hval x, h2, hop]
        simp at ha
        rcases ha with ha | ha <;> subst ha <;> simp [GateOp.eval, hsubB, hBj]⟩
    · by_cases hr : r = a.val
      · by_cases hs : s = a.val
        · exact ⟨j, const_false n C1 j hj1 fun x => by
            rw [hval x, h2, hop, hr, hs]; simp [GateOp.eval, hsubB, hBj]⟩
        · obtain ⟨p, hp⟩ := pass_through n C1 j s hj1 fun x => by
            rw [hval x, h2, hop, hr]; simp [GateOp.eval, hsubB, hBj, hsubr s hs]
          exact ⟨j, p, hp⟩
      · have hs : s = a.val := by simp at ha; omega
        obtain ⟨p, hp⟩ := pass_through n C1 j r hj1 fun x => by
          rw [hval x, h2, hop, hs]; simp [GateOp.eval, hsubB, hBj, hsubr r hr]
        exact ⟨j, p, hp⟩
    · have := hnu _ (List.getElem_mem hj) hop
      rw [h2] at this; simp at this

theorem elim_one (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hnu : NotUnary C) (a : Fin n) (x : Fin n → Bool)
    (hne : C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x a false)))
    (hout : C.output ≠ a.val) (y0 : Fin n → Bool)
    (hy0 : C.eval (List.ofFn (Function.update y0 a false)) = false) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ NotUnary C' ∧ C'.size + 1 ≤ C.size ∧
      ∀ z, C'.eval (List.ofFn z) = C.eval (List.ofFn (Function.update z a false)) := by
  obtain ⟨j, hj, heq, hd⟩ := first_diff n C a x hne hout
  have ha := reads_a n C a x j hj heq hd
  set C1 := fixC a a C (n + C.gates.length) with hC1
  have hev : ∀ z, C1.eval (List.ofFn z) = C.eval (List.ofFn (Function.update z a false)) := by
    intro z
    rw [hC1, fix_eval, Function.update_idem]
  obtain ⟨m, p, hm, hp, hc⟩ := erasable_fixed n C hC hnu a j hj ha y0 (by rw [hev]; exact hy0)
  refine ⟨eraseGate n C1 m p, erase_fanin n C1 m p hm (fix_fanin _ _ _ C hC),
    erase_notu n C1 m p hm (fix_notu _ _ _ C hnu), ?_, fun z => ?_⟩
  · have h1 := erase_size n C1 m p hm
    have h2 : C1.size = C.size := fix_size _ _ _ C
    omega
  · rw [erase_eval n C1 m p (List.ofFn z) (by simp) hm hp ?_, hev]
    rcases hc with hc | hc
    · exact Or.inl (hc z)
    · exact Or.inr hc

def P {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  (∃ b ∈ B, x b = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

theorem induct (n : ℕ) (G : SimpleGraph (Fin n)) (hedge : ∃ u v : Fin n, G.Adj u v) :
    ∀ B : Finset (Fin n), (∀ u v, G.Adj u v → u ∉ B) → ∀ C : Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → NotUnary C →
      (∀ x, C.eval (List.ofFn x) = true ↔ P G B x) →
      ∃ C' : Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size + B.card ≤ C.size ∧
        ∀ x, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _ C hC _ hev
    refine ⟨C, hC, by simp, fun x => ?_⟩
    rw [hev x]
    simp [P]
  | insert a B haB ih =>
    intro hiso C hC hnu hev
    obtain ⟨u, v, huv⟩ := hedge
    have hua : u ≠ a := fun h => hiso u v huv (by simp [h])
    have hva : v ≠ a := fun h => hiso v u huv.symm (by simp [h])
    have hfalse : ∀ x : Fin n → Bool, (∀ i, x i = false) → C.eval (List.ofFn x) = false := by
      intro x hx
      rcases Bool.eq_false_or_eq_true (C.eval (List.ofFn x)) with h | h
      · exfalso
        rcases (hev x).mp h with ⟨b, -, hb⟩ | ⟨u', v', -, hu', -⟩
        · rw [hx b] at hb; exact Bool.false_ne_true hb
        · rw [hx u'] at hu'; exact Bool.false_ne_true hu'
      · exact h
    have hne : C.eval (List.ofFn (fun i => decide (i = a))) ≠
        C.eval (List.ofFn (Function.update (fun i => decide (i = a)) a false)) := by
      have h0 : C.eval (List.ofFn (Function.update (fun i => decide (i = a)) a false)) = false :=
        hfalse _ (by intro i; by_cases h : i = a <;> simp [Function.update, h])
      have h1 : C.eval (List.ofFn (fun i => decide (i = a))) = true :=
        (hev _).mpr (Or.inl ⟨a, by simp, by simp⟩)
      rw [h0, h1]; decide
    have hout : C.output ≠ a.val := by
      intro h
      have hz := (hev (fun i => decide (i = u ∨ i = v))).mpr
        (Or.inr ⟨u, v, huv, by simp, by simp⟩)
      unfold Circuit.eval at hz
      rw [h, wire_input n C _ a] at hz
      simp at hz
      rcases hz with hz | hz
      · exact hua hz.symm
      · exact hva hz.symm
    obtain ⟨C1, hC1, hnu1, hs1, hev1⟩ := elim_one n C hC hnu a _ hne hout (fun _ => false)
      (hfalse _ (by intro i; by_cases h : i = a <;> simp [Function.update, h]))
    have hev1' : ∀ x, C1.eval (List.ofFn x) = true ↔ P G B x := by
      intro x
      rw [hev1, hev]
      unfold P
      have hupd : ∀ i, i ≠ a → Function.update x a false i = x i :=
        fun i hi => Function.update_of_ne hi _ _
      constructor
      · rintro (⟨b, hb, hbx⟩ | ⟨u', v', huv', hu', hv'⟩)
        · rcases Finset.mem_insert.mp hb with rfl | hb
          · simp at hbx
          · have hba : b ≠ a := fun h => haB (h ▸ hb)
            exact Or.inl ⟨b, hb, by rwa [hupd b hba] at hbx⟩
        · have hu'a : u' ≠ a := fun h => hiso u' v' huv' (by simp [h])
          have hv'a : v' ≠ a := fun h => hiso v' u' huv'.symm (by simp [h])
          exact Or.inr ⟨u', v', huv', by rwa [hupd u' hu'a] at hu', by rwa [hupd v' hv'a] at hv'⟩
      · rintro (⟨b, hb, hbx⟩ | ⟨u', v', huv', hu', hv'⟩)
        · have hba : b ≠ a := fun h => haB (h ▸ hb)
          exact Or.inl ⟨b, Finset.mem_insert_of_mem hb, by rwa [hupd b hba]⟩
        · have hu'a : u' ≠ a := fun h => hiso u' v' huv' (by simp [h])
          have hv'a : v' ≠ a := fun h => hiso v' u' huv'.symm (by simp [h])
          exact Or.inr ⟨u', v', huv', by rwa [hupd u' hu'a], by rwa [hupd v' hv'a]⟩
    obtain ⟨C', hC', hs', hev'⟩ := ih (fun u' v' h hu' => hiso u' v' h (Finset.mem_insert_of_mem hu'))
      C1 hC1 hnu1 hev1'
    refine ⟨C', hC', ?_, hev'⟩
    rw [Finset.card_insert_of_notMem haB]
    omega

end PEqualNP.Outside.L_meta_4119

theorem PEqualNP.Outside.L_meta_4119 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ (x6 x7 : Fin x1), x3.Adj x6 x7 → x6 ∉ x4) → (∃ (x7 : Fin x1) (x8 : Fin x1), x3.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x5 x8 = Bool.true ↔ (∃ x9 ∈ x4, x8 x9 = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x2 → ∃ (x10 : ℕ), x10 + x4.card ≤ x2 ∧ ∃ (x11 : (Fin x1 → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize x1 x11 x10 ∧ ∀ (x12 : Fin x1 → Bool), x11 x12 = Bool.true ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true := by
  intro n s G A f hiso hedge hf hsize
  obtain ⟨C0, hfan, hsz, hev⟩ := hsize
  obtain ⟨C', hC', hs', hev'⟩ := PEqualNP.Outside.L_meta_4119.induct n G hedge A hiso
    (PEqualNP.Outside.L_meta_4119.normC C0) (PEqualNP.Outside.L_meta_4119.norm_fanin C0 hfan)
    (PEqualNP.Outside.L_meta_4119.norm_notu C0)
    (fun x => by
      rw [PEqualNP.Outside.L_meta_4119.norm_eval, hev x, hf x]
      rfl)
  refine ⟨C'.size, ?_, fun x => C'.eval (List.ofFn x), ⟨C', hC', le_rfl, fun x => rfl⟩, hev'⟩
  have := PEqualNP.Outside.L_meta_4119.norm_size C0
  omega
