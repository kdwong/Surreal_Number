import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax

inductive Game where
  | mk : List Game → List Game → Game

open Game

def Game.left (g : Game) : List Game :=
  match g with
  | mk left _ => left

def Game.right (g : Game) : List Game :=
  match g with
  | mk _ right => right

def zero : Game := mk [] []
def minus_one : Game := mk [] [zero]
def one : Game := mk [zero] []
def half : Game := mk [zero] [one]

def Game.birthday (g : Game) : Nat :=
  match g with
  | mk L R =>
    let bL := L.map birthday
    let bR := R.map birthday
    (bL ++ bR).maximum.getD 0 + 1

#eval birthday zero
#eval birthday half -- 3

lemma list_maximum_is_none_then_is_empty (a : List ℕ) (non : a.maximum = none) : a = [] := by
  cases a with
  | nil => rfl
  | cons hd tl =>
    have ne_none : (hd :: tl).maximum ≠ none := by
      apply List.maximum_ne_bot_of_ne_nil
      simp
    contradiction

lemma elt_leq_max (a : List ℕ) (s : ℕ) (h : s ∈ a) : s ≤ a.maximum.getD 0 := by
    match max : a.maximum with
    | none =>
      have a_empty : a = [] := by
        apply list_maximum_is_none_then_is_empty a max
      rw [a_empty] at h
      contradiction
    | some m =>
      simp [Option.getD_some]
      exact List.le_of_mem_argmax h max

lemma birthday_lt_left (g : Game) (l : Game) (h : l ∈ g.left) :
    birthday l < birthday g := by
  cases g with
  | mk L R =>
    simp [left] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday l < b.maximum.getD 0 + 1
    have h_mem_b : l.birthday ∈ b := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      use l
    have a : l.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b l.birthday h_mem_b
    linarith

lemma birthday_lt_right (g : Game) (r : Game) (h : r ∈ g.right) :
    birthday r < birthday g := by
  cases g with
  | mk L R =>
    simp [right] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday r < b.maximum.getD 0 + 1
    have h_mem_b : r.birthday ∈ b := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      use r
    have aaa : r.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b r.birthday h_mem_b
    linarith

def Game.le (g h : Game) : Prop :=
    (∀ g_l ∈ g.left, ¬(le h g_l)) ∧ (∀ h_r ∈ h.right, ¬(le h_r g))
termination_by (birthday g + birthday h)
decreasing_by
  -- Prove termination for the first recursive call: `le h g_l`
  · have xl : g_l ∈ g.left := by assumption
    rw [add_comm h.birthday g_l.birthday]
    apply add_lt_add_right
    exact birthday_lt_left g g_l xl
  -- Prove termination for the second recursive call: `le h_r g`
  · have xr : h_r ∈ h.right := by assumption
    rw [add_comm h_r.birthday g.birthday]
    apply add_lt_add_left
    exact birthday_lt_right h h_r xr

def Game.lt (g h : Game) : Prop := le g h ∧ ¬(le h g)

def Game.eq (g h : Game) : Prop :=
  le g h ∧ le h g

theorem zero_leq_zero : le zero zero := by
      unfold le
      constructor <;> (intro g h; cases h)

theorem zero_leq_one : le zero one := by
  unfold le
  constructor
  · intro z_l zero_left
    cases zero_left
  · intro o_r one_right
    cases one_right

theorem one_not_leq_zero : ¬(le one zero) := by
  intro h_le
  unfold le at h_le
  let h_not_le_zero_zero := h_le.1 zero (by simp [one, left])
  exact h_not_le_zero_zero zero_leq_zero

theorem half_leq_one : le half one := by
  unfold le
  constructor
  · intro h_l half_left
    simp only [half, left, List.mem_singleton] at half_left
    subst half_left
    exact one_not_leq_zero
  · intro o_r one_right
    cases one_right

theorem zero_lth_one : lt zero one := by
  unfold lt
  constructor
  · exact zero_leq_one
  · intro h_le
    unfold le at h_le
    let h_contra := h_le.1 zero (by simp [one, left])
    exact h_contra zero_leq_zero

def zero' : Game := mk [minus_one] [one]

theorem zero_zero'_eq : eq zero zero' := by
  unfold eq
  constructor
  · -- Prove `zero ≤ zero'`
    unfold le
    constructor
    · intro z_l zero_left
      cases zero_left
    · intro z_r zero'_right
      simp only [zero', right, List.mem_singleton] at zero'_right
      subst zero'_right
      exact one_not_leq_zero
  · -- Prove `zero' ≤ zero`
    unfold le
    constructor
    · intro z'_l zero'_left
      simp only [zero', left, List.mem_singleton] at zero'_left
      subst z'_l
      intro h_le_zero_neg_one
      unfold le at h_le_zero_neg_one
      let h_contra := h_le_zero_neg_one.2 zero (by simp [minus_one, right])
      exact h_contra zero_leq_zero
    · intro z_r zero_right
      cases zero_right

def R : Game → Game → Prop := fun y x => birthday y < birthday x
lemma wf_R : WellFounded R := InvImage.wf birthday wellFounded_lt


-- This is an exercise. The solution is given below.
theorem x_le_x' : ∀ (x : Game), le x x := by
  intro x
  apply wf_R.induction x
  intro x IH
  unfold le
  unfold R at IH
  constructor
  · -- for l ∈ x.left, prove ¬(x ≤ l)
    sorry
  · -- for r ∈ x.right, prove ¬(r ≤ x)
    sorry



theorem x_le_x : ∀ (x : Game), le x x := by
  intro x
  apply wf_R.induction x
  intro x IH
  unfold le
  unfold R at IH

  constructor
  · -- for l ∈ x.left, prove ¬(x ≤ l)
    intro l hl h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.1 l (by simp[left]; exact hl)
    have h_le: le l l := IH l (birthday_lt_left x l hl)
    contradiction

  · -- for r ∈ x.right, prove ¬(r ≤ x)
    intro r hr h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.2 r (by simp[right]; exact hr)
    have h_le: le r r := IH r (birthday_lt_right x r hr)
    contradiction

theorem x_eq_x : ∀ (x : Game), eq x x := by
  intro x
  unfold eq
  constructor
  · exact x_le_x x
  · exact x_le_x x
