import Mathlib

abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) := 
  {p | ∃ d : ℤ, d ∣ (2018 : ℤ)^2 ∧ 
         p.1 = (d + 2018) / 3 ∧ 
         p.2 = ((2018 : ℤ)^2 / d + 2018) / 3 ∧
         0 < p.1 ∧ 0 < p.2 ∧
         3 ∣ (d + 2018) ∧ 3 ∣ ((2018 : ℤ)^2 / d + 2018)}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · intro h_eq
    have h₁ : 0 < a := h.1
    have h₂ : 0 < b := h.2
    -- Transform the equation: 1/a + 1/b = 3/2018
    -- Multiply by ab: b + a = 3ab/2018
    -- Rearrange: 2018(a+b) = 3ab
    -- Multiply by 3: 6054(a+b) = 9ab
    -- Complete the rectangle: (3a-2018)(3b-2018) = 2018²
    
    have h₃ : (3 * a - 2018 : ℤ) * (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 := by
      field_simp [h₁.ne', h₂.ne'] at h_eq
      ring_nf at h_eq ⊢
      norm_cast at h_eq ⊢
      linarith
    
    let d := 3 * a - 2018
    have h₄ : d ∣ (2018 : ℤ)^2 := by
      use 3 * b - 2018
      rw [h₃]
    
    have h₅ : 3 ∣ (d + 2018) := by
      have : d + 2018 = 3 * a := by ring
      rw [this]
      exact ⟨a, by ring⟩
    
    have h₆ : 3 ∣ ((2018 : ℤ)^2 / d + 2018) := by
      have h₇ : (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 / d := by
        have h₈ : d ≠ 0 := by
          intro h₉
          rw [h₉] at h₄
          simp at h₄
        have h₉ : d * (3 * b - 2018) = (2018 : ℤ)^2 := by
          rw [h₃]
        field_simp [h₈] at h₉ ⊢
        linarith
      have : (2018 : ℤ)^2 / d + 2018 = 3 * b := by
        rw [h₇]
        ring
      rw [this]
      exact ⟨b, by ring⟩
    
    refine' ⟨d, h₄, _, _, h₂, h₅, h₆⟩
    · have : d + 2018 = 3 * a := by ring
      rw [this]
      exact ⟨a, by ring⟩
    · have h₇ : (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 / d := by
        have h₈ : d ≠ 0 := by
          intro h₉
          rw [h₉] at h₄
          simp at h₄
        have h₉ : d * (3 * b - 2018) = (2018 : ℤ)^2 := by
          rw [h₃]
        field_simp [h₈] at h₉ ⊢
        linarith
      have : (2018 : ℤ)^2 / d + 2018 = 3 * b := by
        rw [h₇]
        ring
      rw [this]
      exact ⟨b, by ring⟩
  
  · rintro ⟨d, hd, ha, hb, hpos, hdiv1, hdiv2⟩
    have h₁ : 0 < a := hpos.1
    have h₂ : 0 < b := hpos.2
    have h₃ : a = (d + 2018) / 3 := by
      rw [ha]
    have h₄ : b = ((2018 : ℤ)^2 / d + 2018) / 3 := by
      rw [hb]
    have h₅ : 3 ∣ (d + 2018) := hdiv1
    have h₆ : 3 ∣ ((2018 : ℤ)^2 / d + 2018) := hdiv2
    have h₇ : d ∣ (2018 : ℤ)^2 := hd
    
    have h₈ : (3 * a - 2018 : ℤ) * (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 := by
      have h₉ : 3 * a = d + 2018 := by
        have h₁₀ : (d + 2018) % 3 = 0 := by
          omega
        have h₁₁ : (d + 2018) / 3 * 3 = d + 2018 := by
          omega
        rw [ha] at h₁₁
        linarith
      have h₁₀ : 3 * b = (2018 : ℤ)^2 / d + 2018 := by
        have h₁₁ : ((2018 : ℤ)^2 / d + 2018) % 3 = 0 := by
          omega
        have h₁₂ : ((2018 : ℤ)^2 / d + 2018) / 3 * 3 = (2018 : ℤ)^2 / d + 2018 := by
          omega
        rw [hb] at h₁₂
        linarith
      calc
        (3 * a - 2018 : ℤ) * (3 * b - 2018 : ℤ)
          = (d + 2018 - 2018 : ℤ) * ((2018 : ℤ)^2 / d + 2018 - 2018 : ℤ) := by
            rw [h₉, h₁₀]
          _ = d * ((2018 : ℤ)^2 / d : ℤ) := by ring
          _ = (2018 : ℤ)^2 := by
            have h₁₁ : d ≠ 0 := by
              intro h₁₂
              rw [h₁₂] at h₇
              simp at h₇
            have h₁₂ : d * ((2018 : ℤ)^2 / d : ℤ) = (2018 : ℤ)^2 := by
              apply Int.mul_ediv_cancel'
              exact h₇
            exact h₁₂
    
    have h₉ : (3 * a - 2018 : ℤ) * (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 := h₈
    have h₁₀ : 2018 * (a + b : ℤ) = 3 * a * b := by
      have h₁₁ : (3 * a - 2018 : ℤ) * (3 * b - 2018 : ℤ) = (2018 : ℤ)^2 := h₈
      ring_nf at h₁₁ ⊢
      linarith
    
    have h₁₁ : (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 := by
      have h₁₂ : 0 < a := h₁
      have h₁₃ : 0 < b := h₂
      field_simp [h₁₂.ne', h₁₃.ne']
      norm_cast at h₁₀ ⊢
      linarith
    
    exact h₁₁
