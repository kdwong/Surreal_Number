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
-- just list of games satisfying IsSurreal (rather than list of surreals).
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


theorem Surreal.le_refl (x : Surreal) : Surreal.le x x := by
  unfold Surreal.le
  apply x_le_x

theorem Surreal.le_trans : ∀ x y z : Surreal ,
  (Surreal.le x y) ∧ (Surreal.le y z) → Surreal.le x z := by
  unfold Surreal.le
  intro x y z h_le
  exact Game.le_trans x.val y.val z.val h_le


def S : Surreal → Surreal → Prop := fun y x => birthday y < birthday x
lemma wf_S : WellFounded S :=
  InvImage.wf (fun s : Surreal => birthday s) wellFounded_lt


-- Prove that for any surreal number x = {xl ∈ XL | xr ∈ XR}, xl < x and x < xr
-- The proof requires the fact that x is surreal.
-- This is an exercise. The solution is given below.
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
