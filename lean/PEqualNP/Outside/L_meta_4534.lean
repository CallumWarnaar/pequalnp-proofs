import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4
  dsimp only
  intro h12 h3 h34 k
  obtain ⟨i, hi⟩ := k
  have hlen : i < x2.length + x4.length := by simpa using hi
  by_cases h : i < x2.length
  · obtain ⟨a, ha, b, hb, hab⟩ := h12 ⟨i, h⟩
    have ht : List.take i (x2 ++ x4) = List.take i x2 := List.take_append_of_le_length (le_of_lt h)
    have hg : (x2 ++ x4).get ⟨i, hi⟩ = x2.get ⟨i, h⟩ := by
      simp [List.getElem_append_left h]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab
  · have hj : i - x2.length < x4.length := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := h34 ⟨i - x2.length, hj⟩
    have ht : List.take i (x2 ++ x4) = x2 ++ List.take (i - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le (by omega)]
    have hg : (x2 ++ x4).get ⟨i, hi⟩ = x4.get ⟨i - x2.length, hj⟩ := by
      simp [List.getElem_append_right (by omega : x2.length ≤ i)]
    have hmem : ∀ c ∈ x3 ++ List.take (i - x2.length) x4,
        c ∈ x1 ++ (x2 ++ List.take (i - x2.length) x4) := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp (h3 c hc) with hc' | hc'
        · exact List.mem_append_left _ hc'
        · exact List.mem_append_right _ (List.mem_append_left _ hc')
      · exact List.mem_append_right _ (List.mem_append_right _ hc)
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact hmem a ha
    · rw [ht]; exact hmem b hb
    · rw [hg]; exact hab
