import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import LeanProject.Surreal_Number.game

open Game

-- Surreal numbers are defined as games where all left and right options are surreal numbers,
-- and no left option is greater than or equal to any right option
def IsSurreal (g : Game) : Prop :=
  (∀ g_l ∈ g.left, ∀ g_r ∈ g.right, ¬(le g_r g_l)) ∧
  (∀ g_l ∈ g.left, IsSurreal g_l) ∧ (∀ g_r ∈ g.right, IsSurreal g_r)
termination_by g.birthday
decreasing_by
  · have xl : g_l ∈ g.left := by assumption
    apply birthday_lt_left g g_l xl
  · have xr : g_r ∈ g.right := by assumption
    apply birthday_lt_right g g_r xr


def Surreal := { g : Game // IsSurreal g }

-- Caution: g is a surreal number type, but g.left and g.right are
-- just list of games satisfying IsSurreal.
instance : Coe Surreal Game where
  coe := Subtype.val
def Surreal.left (s : Surreal) : List Game := s.val.left
def Surreal.right (s : Surreal) : List Game := s.val.right
def Surreal.le (s t : Surreal) : Prop := Game.le (s.val) (t.val)

lemma isSurreal_zero : IsSurreal zero := by
  unfold IsSurreal
  constructor
  · simp [zero, Game.left, Game.right]
  · constructor
    · simp [zero, Game.left]
    · simp [zero, Game.right]
def sr_zero : Surreal := ⟨zero, isSurreal_zero⟩
#check sr_zero.val -- Game
#check sr_zero.property -- IsSurreal sr_zero

def S : Surreal → Surreal → Prop := fun y x => birthday y < birthday x
lemma wf_S : WellFounded S :=  by
  exact InvImage.wf (fun s : Surreal => birthday s) wellFounded_lt



-- Prove that for any surreal number x = {xl ∈ XL | xr ∈ XR}, xl < x and x < xr
-- The proof requires the fact that x is surreal.
-- This is an exercise. The solution is given below.
theorem xL_x_xR' : ∀ (x : Surreal),
  (∀ x_l ∈ x.left, lt x_l x) ∧ (∀ x_r ∈ x.right, lt x x_r) := by
  intro x
  apply wf_S.induction x
  intro y IH
  constructor
  · intro y_l h_yl
    unfold lt
    constructor
    · -- for y_l ∈ y.left, prove y_l ≤ y
      sorry
    · -- for y_l ∈ y.left, prove ¬(y ≤ y_l)
      sorry
  · intro y_r h_yr
    unfold lt
    constructor
    · -- for y_r ∈ y.right, prove y ≤ y_r
      sorry
    · -- for y_r ∈ y.right, prove ¬(y_r ≤ y)
      sorry


theorem xL_x_xR : ∀ (x : Surreal),
  (∀ x_l ∈ x.left, lt x_l x) ∧ (∀ x_r ∈ x.right, lt x x_r) := by
  intro x
  apply wf_S.induction x
  intro y IH
  constructor
  · intro y_l h_yl
    unfold lt
    constructor
    · -- for y_l ∈ y.left, prove y_l ≤ y
      unfold le
      constructor
      · -- for y_ll ∈ y_l.left, prove ¬(y ≤ y_ll)
        intro y_ll h_yll y_contra
        have y_surreal := y.property
        unfold IsSurreal at y_surreal
        have yl_surreal := y_surreal.2.1 y_l (by simp [left]; exact h_yl)
        unfold le at y_contra
        have h_contra := y_contra.1 y_l (by simp [left]; exact h_yl)
        unfold S at IH
        have h1 := IH ⟨y_l, yl_surreal⟩ (birthday_lt_left y y_l h_yl)
        have h2 := h1.1 y_ll (by simp [Surreal.left]; exact h_yll)
        unfold lt at h2
        have h3 := h2.1
        contradiction
      · -- for y_r ∈ y.right, prove ¬(y_r ≤ y_l)
        -- this is the part where surreal property is used
        intro y_r h_yr
        have h_surreal := y.property
        unfold IsSurreal at h_surreal
        have h1 := h_surreal.1 y_l h_yl y_r h_yr
        exact h1

    · -- for y_l ∈ y.left, prove ¬(y ≤ y_l)
      intro y_le_y_l
      unfold le at y_le_y_l
      let h_contra := y_le_y_l.1 y_l (by simp [left]; exact h_yl)
      have h : le y_l y_l := by exact x_le_x y_l
      contradiction
  · intro y_r h_yr
    unfold lt
    constructor
    · -- for y_r ∈ y.right, prove y ≤ y_r
      unfold le
      constructor
      · -- for y_l ∈ y.left, prove ¬(y_r ≤ y_l)
        intro y_l h_yl
        have h_surreal := y.property
        unfold IsSurreal at h_surreal
        have h1 := h_surreal.1 y_l h_yl y_r (by simp [right]; exact h_yr)
        exact h1
      · -- for y_rr ∈ y_r.right, prove ¬(y_rr ≤ y)
        intro y_rr h_yrr y_contra
        have y_surreal := y.property
        unfold IsSurreal at y_surreal
        have yr_surreal := y_surreal.2.2 y_r (by simp [right]; exact h_yr)
        unfold le at y_contra
        have h_contra := y_contra.2 y_r (by simp [right]; exact h_yr)
        unfold S at IH
        have h1 := IH ⟨y_r, yr_surreal⟩ (birthday_lt_right y y_r h_yr)
        have h2 := h1.2 y_rr (by simp [Surreal.right]; exact h_yrr)
        unfold lt at h2
        have h3 := h2.1
        contradiction
    · -- for y_r ∈ y.right, prove ¬(y_r ≤ y)
      intro y_r_le_y
      unfold le at y_r_le_y
      let h_contra := y_r_le_y.2 y_r (by simp [right]; exact h_yr)
      have h : le y_r y_r := by exact x_le_x y_r
      contradiction
