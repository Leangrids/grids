import data.int.basic

namespace utils 

open int nat list

lemma gt_both_of_mult {m n : ℕ} (h : m * n > 0) : m > 0 ∧ n > 0 :=
and.intro
  begin
    cases m,
      {rw zero_mul at h, cases h},
      {apply nat.zero_lt_succ}
  end
  begin
    cases n, 
      {cases h},
      {apply nat.zero_lt_succ}
  end

lemma gt_mult_of_both {m n : ℕ} (h : m > 0) (h₁ : n > 0) : m * n > 0 :=
begin
  suffices h₂ : 0 * n < m * n,
    rw zero_mul at h₂, exact h₂,
  apply mul_lt_mul_of_pos_right; assumption
end

lemma lt_of_coe_lt_gt_zero {x : ℤ} {y : ℕ} (h : y > 0) : x < x + ↑y :=
begin
  apply lt_add_of_pos_right,
  simp [(>)] at *,
  exact h
end

lemma lt_of_add {m n k : ℕ} (h : m + n < k) : m < k :=
begin
  induction n with n ih,
    {exact h},
    {
      apply ih,
      rw [add_comm, nat.succ_add] at h,
      have h : n + m < k,
        from nat.lt_of_succ_lt h,
      rw add_comm,
      exact h
    }
end

lemma nat_le_dest : ∀ {n m : ℕ}, n < m → ∃ k, nat.succ n + k = m
  | n ._ (less_than_or_equal.refl ._)  := ⟨0, rfl⟩
  | n ._ (@less_than_or_equal.step ._ m h) :=
    match le.dest h with
      | ⟨w, hw⟩ := ⟨succ w, hw ▸ rfl⟩
    end

lemma zip_nil_right {α β : Type} {l : list α} : zip l ([] : list β) = [] :=
  by cases l; refl

lemma zip_nil_iff {α β : Type} (l₁ : list α) (l₂ : list β) :
  list.zip l₁ l₂ = [] ↔ l₁ = [] ∨ l₂ = [] :=
iff.intro (λh, by cases l₁; cases l₂; finish)
          (λh, begin cases h with h₁ h₁; rw h₁;
                     unfold zip zip_with,
                     exact zip_nil_right end)

lemma zip_with_len_l {α β γ : Type*} {l₁ : list α} {l₂ : list β} {f : α → β → γ}
  (h : length l₁ = length l₂) : length (zip_with f l₁ l₂) = length l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {simp [zip_with]},
    {
      cases l₂ with y ys,
        {injection h},
        {
          simp only [zip_with, length],
          rw ih, injection h
        }
    }
end

lemma zip_with_len_r {α β γ : Type*} {l₁ : list α} {l₂ : list β} {f : α → β → γ}
  (h : length l₁ = length l₂) : length (zip_with f l₁ l₂) = length l₂ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {rw ← h, simp [zip_with]},
    {
      cases l₂ with y ys,
        {injection h},
        {
          simp only [zip_with, length],
          rw ih, injection h
        }
    }
end

lemma repeat_nil {α : Type} (x : α) (n : ℕ) : list.repeat x n = [] ↔ n = 0 :=
iff.intro (λh, begin
                 cases n,
                   refl,
                 unfold list.repeat at h,
                 cases h
               end)
          (λh, by rw h; refl)

lemma nat_abs_zero_iff (a b : ℤ) : nat_abs (a - b) = 0 ↔ a = b :=
iff.intro begin generalize h : a - b = c, intros,
                cases c; dsimp at a_1, rw a_1 at h,
                  apply eq_of_sub_eq_zero,
                  rw of_nat_zero at h,
                  exact h,
                cases a_1
          end
          begin generalize h : a - b = c, intros,
                rw a_1 at h, rw sub_self at h,
                rw ← h, refl
          end

lemma join_empty_of_all_empty {α : Type*} (xs : list (list α)) 
  (h : (∀x, x ∈ xs → x = [])) : join xs = [] :=
begin
  induction xs with x xs ih,
    {refl},
    {
      unfold join,
      have h₁ : x = [], from h _ (by left; refl),
      rw h₁, rw nil_append,
      apply ih, intros x₁,
      specialize h x₁, intros h₂,
      apply h, right, exact h₂
    }
end

lemma repeat_more {α : Type} (x : α) (n : ℕ) (h : n ≥ 1) :
  repeat x n = x :: repeat x (n - 1) :=
begin
  cases n, cases h,
  dsimp, apply congr_arg, rw sub_one,
  refl
end

lemma one_le_succ (a : ℕ) : 1 ≤ nat.succ a :=
begin
  induction a,
    exact le_refl _,
  constructor, exact a_ih
end

lemma nat_abs_of_lt {a b : ℤ} (h : a < b) : nat_abs (b - a) ≥ 1 :=
have h₁ : b - a > 0, from sub_pos_of_lt h,
begin
  simp only [(≥)],
  rw [← coe_nat_le, nat_abs_of_nonneg (int.le_of_lt h₁), int.coe_nat_one],
  conv { to_lhs, rw ← zero_add (1 : ℤ) },
  apply add_one_le_of_lt,
  exact h₁
end

lemma neg_lt_of_succ (n : ℕ) (a : ℤ) (h : a ≥ 0) : -↑n < a + (1 : ℤ) :=
have h₁ : -↑n ≤ (0 : ℤ), {rw neg_le, rw neg_zero, trivial},
have h₂ : 0 < a + 1, {rw lt_add_one_iff, exact h},
lt_of_le_of_lt h₁ h₂

section bounded

variables {α : Type} [decidable_linear_order α]

def bounded (a b : α) :=
  {x : α // a ≤ x ∧ x < b}

def is_bounded (a b : α) (y : α) :=
  a ≤ y ∧ y < b

lemma is_bounded_of_bounds {a b y : α} (h : a ≤ y) (h₁ : y < b) :
  is_bounded a b y := and.intro h h₁

instance is_bounded_dec (a b y : α) : decidable (is_bounded a b y) :=
  by simp [is_bounded]; apply_instance

def make_bounded {a b : α} {x : α} (h : is_bounded a b x) : bounded a b :=
  ⟨x, h⟩

def z_of_bounded {a b : α} (b : bounded a b) :=
  match b with ⟨z, _⟩ := z end

def bounded_to_str [φ : has_to_string α] {a b : α} :
  bounded a b → string := to_string ∘ z_of_bounded

instance bounded_repr {a b : α} [has_to_string α] :
  has_repr (bounded a b) := ⟨bounded_to_str⟩

instance bounded_str (a b : α) [has_to_string α] :
  has_to_string (bounded a b) := ⟨bounded_to_str⟩

instance bounded_to_carrier_coe (a b : α) : has_coe (bounded a b) α :=
  ⟨z_of_bounded⟩

instance zbound_dec_eq {a b : α} : decidable_eq (bounded a b)
  | ⟨x, _⟩ ⟨y, _⟩ := by apply_instance

instance coe_bounded {α : Type} {a b : α} [decidable_linear_order α] :
  has_coe (@bounded α _ a b) α := ⟨z_of_bounded⟩

lemma coe_is_z_of_bounded {α : Type} {a b : α} [decidable_linear_order α]
  (x : bounded a b) : z_of_bounded x = ↑x := rfl

lemma positive_bounded {x : ℕ} (a : bounded 0 x) : ↑a ≥ 0 :=
let ⟨a, ⟨l, r⟩⟩ := a in by rw ← coe_is_z_of_bounded; simpa [z_of_bounded]

lemma bounded_lt {x : ℕ} (a : bounded 0 x) : ↑a < x :=
let ⟨a, ⟨l, r⟩⟩ := a in by rw ← coe_is_z_of_bounded; simpa [z_of_bounded]

end bounded

structure point := (x : ℤ) (y : ℤ)

private def point_rep : point → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

def point_eq (p₁ p₂ : point) := p₁.x = p₂.x ∧ p₁.y = p₂.y

instance dec_eq_p {p₁ p₂} : decidable (point_eq p₁ p₂) :=
  by simp [point_eq]; apply_instance

instance dec_eq_point : decidable_eq point :=
  λ⟨x₁, y₁⟩ ⟨x₂, y₂⟩,
  begin
    by_cases h₁ : x₁ = x₂;
    by_cases h₂ : y₁ = y₂,
      {
        apply is_true,
          rw h₁, rw h₂
      },
      {
        apply is_false,
          rw h₁, intros contra,
          injection contra, contradiction
      },
      {
        apply is_false,
          rw h₂, intros contra,
          injection contra, contradiction
      },
      {
        apply is_false,
          intros contra, injection contra,
          contradiction
      } 
  end

instance : has_to_string point := ⟨point_rep⟩

instance : has_repr point := ⟨point_rep⟩

def grid_sorted : point → point → Prop
  | ⟨x, y⟩ ⟨x₁, y₁⟩ := x < x₁ ∧ y₁ < y

infix `↗` : 50 := grid_sorted

instance {a b : point} : decidable (a ↗ b) :=
  let ⟨x, y⟩ := a in
  let ⟨x₁, y₁⟩ := b in by simp [(↗)]; apply_instance

instance {a b : point} : is_irrefl point grid_sorted := {
  irrefl := λ⟨x, y⟩, begin
                      simp [(↗)], intros contra,
                      refl
                    end
}

instance {a b : point} : is_trans point grid_sorted := {
  trans := λ⟨x, y⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨h, h₁⟩ ⟨h₂, h₃⟩,
             begin
               simp [(↗)] at *,
               exact and.intro (lt_trans h h₂) (lt_trans h₃ h₁)
             end
}

instance {a b : point}
         [c : is_irrefl point grid_sorted]
         [c₁ : is_trans point grid_sorted] :
         is_strict_order point grid_sorted := by constructor; assumption

def le_of_add_le_left (a b c : ℤ) (h₁ : 0 ≤ b) (h₂ : a + b ≤ c) : a ≤ c :=
begin
  apply (@le_of_add_le_add_right _ _ a b c),
  apply le_add_of_le_of_nonneg; assumption
end

lemma grid_bounded_iff {p₁ p₂ : point} : p₁↗p₂ ↔ (p₁.x < p₂.x ∧ p₂.y < p₁.y) :=
  by cases p₁; cases p₂; simp [(↗)]

lemma length_zip_left {α β : Type*} {l₁ : list α} {l₂ : list β}
  (h : length l₁ = length l₂) : length (zip l₁ l₂) = length l₁ :=
begin
  induction l₁ generalizing l₂; cases l₂,
    refl, 
    cases h,
    cases h,
  unfold zip zip_with,
  dsimp,
  repeat {rw add_one},
  apply congr_arg,
  apply l₁_ih,
  dsimp at h, injection h
end

lemma not_grid_bounded_iff {p₁ p₂ : point} :
  ¬p₁↗p₂ ↔ (p₂.x ≤ p₁.x ∨ p₁.y ≤ p₂.y) :=
begin
  cases p₁; cases p₂,
  unfold point.x point.y,
  simp [(↗)],
  split; intros h,
  {
    by_cases h₁ : p₁_x < p₂_x,
    have h := h h₁,
    right, exact h,
    rw not_lt_iff_eq_or_lt at h₁,
    cases h₁, rw h₁, left, refl,
    left, apply int.le_of_lt, assumption
  },
  {
    intros h₁,
    cases h,
    have contra : p₁_x < p₁_x, from lt_of_lt_of_le h₁ h,
    have contra₁ : ¬p₁_x < p₁_x, from lt_irrefl _,
    contradiction,
    exact h
  }
end

lemma abs_nat_lt : ∀n m : ℤ, (0 ≤ n) → n < m → nat_abs n < nat_abs m
  | (of_nat n₁) (of_nat n₂) zlen nltm :=
  begin
    dsimp,
    revert n₁, induction n₂; intros; cases n₁,
    {cases nltm},
    {cases nltm},
    {apply zero_lt_succ},
    {apply succ_lt_succ,
     apply n₂_ih,
       {cases n₁, apply le_refl,
        rewrite of_nat_succ, rewrite add_comm,
        unfold has_le.le},
       {rewrite of_nat_succ at nltm,
        rewrite of_nat_succ at nltm,
        apply lt_of_add_lt_add_right nltm}
       }
  end

def range_weaken_lower_any {a b c : ℤ} (h : c ≤ a) : bounded a b → bounded c b
  | ⟨i, ⟨lbound, rbound⟩⟩ :=
    ⟨i, and.intro
          (le_trans h lbound)
          rbound⟩

def range_weaken_upper_any {a b c : ℤ} (h : b ≤ c) : bounded a b → bounded a c
  | ⟨i, ⟨lbound, rbound⟩⟩ :=
    ⟨i, and.intro
          lbound
          (have h : b < c ∨ b = c, from lt_or_eq_of_le h,
           or.elim h
            (assume h, lt_trans rbound h)
            (by cc))⟩

def range_weaken {a b : ℤ} (h : bounded (a + 1) b) : bounded a b
  := range_weaken_lower_any
       (le_of_add_le_left _ 1 _ dec_trivial (le_refl _)) h

def range : ∀(a b : ℤ), list (bounded a b) 
  | fro to := if h : fro < to
              then ⟨fro, and.intro (le_refl _) h⟩
                   :: list.map range_weaken (range (fro + 1) to)
              else []
  using_well_founded {
    rel_tac := λf args,
      `[exact ⟨
          measure (λ⟨fro, to⟩, nat_abs (to - fro)),
          measure_wf _
        ⟩],
    dec_tac := `[apply abs_nat_lt,
                   {rewrite ← sub_sub,
                    have h₁ : 0 < to - fro,
                      apply sub_pos_of_lt, exact h,
                    have h₂ : 0 + 1 < (to - fro) + 1,
                      apply add_lt_add_of_lt_of_le,
                      exact h₁, reflexivity,
                    have h₃ : (0 + 1 : ℤ) = 1,
                      exact dec_trivial,
                    rw h₃ at h₂,
                    have h₄ : (0 + 1 ≤ to - fro - 1 + 1) → 0 ≤ to - fro - 1,
                      exact le_of_add_le_add_right,
                    apply h₄, rw h₃,
                    rewrite sub_eq_add_neg,
                    rewrite sub_eq_add_neg,
                    rewrite add_assoc,
                    have h₅ : (-1 + 1 : ℤ) = 0,
                      exact dec_trivial,
                    rewrite h₅,
                    rewrite add_assoc,
                    rewrite add_comm,
                    rewrite add_zero,
                    rewrite add_comm,
                    have h₆ : to + -fro = to - fro,
                      refl,
                    rewrite h₆,
                    unfold has_lt.lt int.lt at h₁,
                    rewrite h₃ at h₁,
                    exact h₁},
                   {rewrite ← sub_sub,
                    apply lt_of_le_sub_one,
                    reflexivity}]
  }

def range_pure : ℤ → ℤ → list ℤ
  | fro to :=  if h : fro < to
               then fro :: range_pure (fro + 1) to else []
  using_well_founded {
    rel_tac := λf args,
      `[exact ⟨
          measure (λ⟨a, b⟩, nat_abs (b - a)),
          measure_wf _
        ⟩],
    dec_tac := `[
      apply abs_nat_lt,
                   {
                     rewrite ← sub_sub,
                    have h₁ : 0 < to - fro,
                      apply sub_pos_of_lt, exact h,
                    have h₂ : 0 + 1 < (to - fro) + 1,
                      apply add_lt_add_of_lt_of_le,
                      exact h₁, reflexivity,
                    have h₃ : (0 + 1 : ℤ) = 1,
                      exact dec_trivial,
                    rw h₃ at h₂,
                    have h₄ : (0 + 1 ≤ to - fro - 1 + 1) → 0 ≤ to - fro - 1,
                      exact le_of_add_le_add_right,
                    apply h₄, rw h₃,
                    rewrite sub_eq_add_neg,
                    rewrite sub_eq_add_neg,
                    rewrite add_assoc,
                    have h₅ : (-1 + 1 : ℤ) = 0,
                      exact dec_trivial,
                    rewrite h₅,
                    rewrite add_assoc,
                    rewrite add_comm,
                    rewrite add_zero,
                    rewrite add_comm,
                    have h₆ : to + -fro = to - fro,
                      refl,
                    rewrite h₆,
                    unfold has_lt.lt int.lt at h₁,
                    rewrite h₃ at h₁,
                    exact h₁
                    },
                   {
                     rewrite ← sub_sub,
                    apply lt_of_le_sub_one,
                    reflexivity
                    }
                    ]
  }          

lemma range_pure_cons {a b} {x xs} (h : range_pure a b = x :: xs) :
  range_pure (a + 1) b = xs :=
begin
  have h₁ : a < b,
    {
      by_cases h₂ : a < b,
        {exact h₂},
        {
          unfold1 range_pure at h,
          rw if_neg h₂ at h,
          cases h
        },
    },
  unfold1 range_pure at h,
  rw if_pos h₁ at h,
  injection h
end

lemma range_pure_bounded {a b : ℤ} :
  ∀{c}, c ∈ range_pure a b → is_bounded a b c :=
assume c,
begin
  generalize h : range_pure a b = l,
  induction l with x xs ih generalizing a b; intros h₁,
    {
      cases h₁
    },
    {
      rw mem_cons_iff at h₁,
      cases h₁ with h₁,
        {
          subst h₁,
          unfold1 range_pure at h,
          by_cases h₂ : a < b; simp [h₂] at h,
            {
              cases h with hl hr, subst hl,
              split, refl, exact h₂
            },
            {
              cases h
            }
        },
        {
          have h₂ : a < b,
            {
              by_cases eq : a < b,
                {exact eq},
                {
                  unfold1 range_pure at h,
                  rw if_neg eq at h,
                  cases h
                },
            },
          unfold1 range_pure at h,
          rw if_pos h₂ at h,
          injection h with hl hr,
          have ih₁ := @ih (a + 1) b hr h₁,
          cases ih₁ with lb ub,
          split,
            {
              have lb := lt_of_add_one_le lb,
              exact int.le_of_lt lb
            },
            {
              exact ub
            }
        }
    }
end

def range_pure_m (a b : ℤ) : list ℤ := map z_of_bounded (range a b)

lemma range_empty_iff (a b : ℤ) : range a b = [] ↔ (b ≤ a) :=
begin
  split; intros h,
  {
    unfold1 range at h,
    by_cases h₁ : a < b; simp [h₁] at h,
      {contradiction},
      {finish},
  },
  {
    unfold1 range,
    by_cases h₁ : a < b; simp [h₁],
    have contra : ¬b ≤ a, from not_le_of_gt h₁,
    contradiction
  }
end

lemma range_length_same (a : ℤ) : length (range a a) = 0 :=
begin
  unfold1 range,
  have h : ¬a < a, from lt_irrefl _,
  simp [h]
end

lemma range_length_one (a : ℤ) : length (range a (a + 1)) = 1 :=
begin
  unfold1 range,
  have h : a < a + 1, from lt_add_succ _ _,
  simp [h],
  rw range_length_same
end

lemma range_pure_length_same (a : ℤ) : length (range_pure a a) = 0 :=
begin
  unfold1 range_pure,
  have h : ¬a < a, from lt_irrefl _,
  simp [h]
end

lemma range_pure_length_one (a : ℤ) : length (range_pure a (a + 1)) = 1 :=
begin
  unfold1 range_pure,
  have h : a < a + 1, from lt_add_succ _ _,
  simp [h],
  rw range_pure_length_same
end

lemma range_length {a b : ℤ} (h : a ≤ b) :
  length (range a b) = nat_abs (b - a) :=
begin
  generalize h₁ : nat_abs (b - a) = n,
  induction n with n ih generalizing a b,
    {
      rw nat_abs_zero_iff at h₁,
      rw h₁,
      exact range_length_same _
    },
    {
      have h₂ : a < b,
        begin
          rw le_iff_eq_or_lt at h,
          cases h,
            {
              have h : b = a, by cc,
              rw ← nat_abs_zero_iff at h,
              rw h at h₁, cases h₁
            },
            {exact h}
        end,
      clear h,
      have h₃ : a + 1 ≤ b, from add_one_le_of_lt h₂,
      have h₄ : nat_abs (b - (a + 1)) = n,
        begin
          rw ← sub_sub,
          rw ← int.coe_nat_eq_coe_nat_iff,
          have h₅ : b - a - 1 ≥ (0 : ℤ),
            {
              simp [(≥)],
              rw ← add_le_add_iff_right (1 : ℤ),
              rw zero_add, rw ← sub_eq_add_neg,
              rw add_sub, rw ← sub_eq_add_neg, 
              rw sub_add_cancel,
              rw ← add_le_add_iff_right a,
              rw sub_add_cancel, rw add_comm,
              exact h₃
            },
          rw nat_abs_of_nonneg h₅,
          rw ← add_right_cancel_iff, any_goals {exact (1 : ℤ)},
          rw sub_add_cancel,
          have h₆ : b - a ≥ (0 : ℤ),
            {
              simp [(≥)],
              rw ← sub_lt_sub_iff_right a at h₂,
              rw sub_self at h₂,
              apply int.le_of_lt,
              exact h₂
            },
          rw ← int.coe_nat_eq_coe_nat_iff at h₁,
          rw nat_abs_of_nonneg h₆ at h₁,
          exact h₁
        end,
      have ih := ih h₃ h₄,
      unfold1 range at ih,
      rw le_iff_eq_or_lt at h₃,
      cases h₃,
        {
          have h₇ : ¬a + 1 < b, rw ← h₃, intros contra,
            have h₈ : ¬a + 1 < a + 1, from lt_irrefl _,
            contradiction,
          simp [h₇] at ih,
          rw ← ih, rw ← h₃, rw range_length_one
        },
        {
          simp [h₃] at ih,
          unfold1 range,
          simp [h₂],
          unfold1 range,
          simp [h₃],
          rw ← ih,
          rw ← one_add
        }
    }
end

lemma range_length_pure {a b : ℤ} (h : a ≤ b) :
  length (range_pure a b) = nat_abs (b - a) := 
begin
    generalize h₁ : nat_abs (b - a) = n,
  induction n with n ih generalizing a b,
    {
      rw nat_abs_zero_iff at h₁,
      rw h₁,
      exact range_pure_length_same _
    },
    {
      have h₂ : a < b,
        begin
          rw le_iff_eq_or_lt at h,
          cases h,
            {
              have h : b = a, by cc,
              rw ← nat_abs_zero_iff at h,
              rw h at h₁, cases h₁
            },
            {exact h}
        end,
      clear h,
      have h₃ : a + 1 ≤ b, from add_one_le_of_lt h₂,
      have h₄ : nat_abs (b - (a + 1)) = n,
        begin
          rw ← sub_sub,
          rw ← int.coe_nat_eq_coe_nat_iff,
          have h₅ : b - a - 1 ≥ (0 : ℤ),
            {
              simp [(≥)],
              rw ← add_le_add_iff_right (1 : ℤ),
              rw zero_add, rw ← sub_eq_add_neg,
              rw add_sub, rw ← sub_eq_add_neg, 
              rw sub_add_cancel,
              rw ← add_le_add_iff_right a,
              rw sub_add_cancel, rw add_comm,
              exact h₃
            },
          rw nat_abs_of_nonneg h₅,
          rw ← add_right_cancel_iff, any_goals {exact (1 : ℤ)},
          rw sub_add_cancel,
          have h₆ : b - a ≥ (0 : ℤ),
            {
              simp [(≥)],
              rw ← sub_lt_sub_iff_right a at h₂,
              rw sub_self at h₂,
              apply int.le_of_lt,
              exact h₂
            },
          rw ← int.coe_nat_eq_coe_nat_iff at h₁,
          rw nat_abs_of_nonneg h₆ at h₁,
          exact h₁
        end,
      have ih := ih h₃ h₄,
      unfold1 range_pure at ih,
      rw le_iff_eq_or_lt at h₃,
      cases h₃,
        {
          have h₇ : ¬a + 1 < b, rw ← h₃, intros contra,
            have h₈ : ¬a + 1 < a + 1, from lt_irrefl _,
            contradiction,
          simp [h₇] at ih,
          rw ← ih, rw ← h₃, rw range_pure_length_one
        },
        {
          simp [h₃] at ih,
          unfold1 range_pure,
          simp [h₂],
          unfold1 range_pure,
          simp [h₃],
          rw ← ih,
          rw ← one_add
        }
    }
end

open list function

def empty_list {α : Type} (l : list α) := [] = l

lemma not_empty_of_len {α : Type} {l : list α}
  (h : length l > 0) : ¬empty_list l :=
begin
  simp [empty_list],
  cases l,
    {
      cases h
    },
    {
      trivial
    }
end

lemma empty_list_eq_ex {α : Type} {l : list α} (h : ¬empty_list l) :
  ∃(x : α) (xs : list α), l = x :: xs :=
begin
  cases l,
    unfold empty_list at h, contradiction,
  existsi l_hd, existsi l_tl,
  refl
end

instance decidable_empty_list {α : Type} : ∀l : list α,
  decidable (empty_list l)
  | [] := is_true rfl
  | (x :: _) := is_false (by simp [empty_list])

theorem unempty_nil_eq_false {α : Type} : ¬(empty_list (@nil α)) ↔ false :=
  begin
    simp [empty_list]
  end

def head1 {α : Type} (l : list α) (h : ¬empty_list l) :=
  match l, h with
    | [], p := by rw unempty_nil_eq_false at p; contradiction
    | (x :: _), _ := x
  end

def foldr1 {α : Type} (f : α → α → α) (l : list α) (h : ¬empty_list l) : α :=
  match l, h with
    | [], p := by rw unempty_nil_eq_false at p; contradiction
    | (x :: xs), _ := foldr f x xs
  end

lemma foldr1_unempty_eq_foldr {α : Type} (f : α → α → α) (l : list α)
  (h : ¬empty_list l) : foldr1 f l h = list.foldr f (head1 l h) (tail l) :=
begin
  cases l,
    rw unempty_nil_eq_false at h, contradiction,
  unfold foldr1 head1 tail
end

def min_element {α : Type} [decidable_linear_order α]
  (l : list α) (h : ¬empty_list l) := foldr1 min l h

def max_element {α : Type} [decidable_linear_order α]
  (l : list α) (h : ¬empty_list l) := foldr1 max l h

lemma foldr_swap {α : Type*}
  (f : α → α → α) (h : is_commutative _ f) (h₁ : is_associative _ f)
  {x y : α} {xs : list α} :
  foldr f x (y :: xs) = foldr f y (x :: xs) :=
have comm : ∀a b, f a b = f b a, by finish,
have assoc : ∀a b c, f a (f b c) = f (f a b) c, by finish,
list.rec_on xs
  (comm _ _) 
  (assume x₁ xs₁ ih,
   by dsimp at *;
      rw [assoc, comm y, ← assoc, ih, assoc, comm x₁, ← assoc])

lemma le_min_elem_all {α : Type*} [decidable_linear_order α]
  (l : list α) (b : α) (h : ¬empty_list l) :
  (∀x, x ∈ l → b ≤ x) → b ≤ min_element l h :=
assume h₁,
begin
  induction l with y ys ih,
    {
      unfold empty_list at h, contradiction
    },
    {
      unfold min_element foldr1,
      cases ys,
        {
          dsimp, apply h₁, left, refl
        },
        {
          have ih := ih _ _,
          unfold min_element foldr1 at ih,
          rw foldr_swap min ⟨min_comm⟩ ⟨min_assoc⟩,
          dsimp at *,
          rw le_min_iff,
          split,
            {
              apply h₁, left, refl
            },
            {
              exact ih_1
            },
          unfold empty_list, intros ok, cases ok,
          intros, apply h₁, right, simp [(∈)] at a, exact a
        }
    }
end

lemma max_le_elem_all {α : Type*} [decidable_linear_order α]
  (l : list α) (b : α) (h : ¬empty_list l) :
  (∀x, x ∈ l → x ≤ b) → max_element l h ≤ b :=
assume h₁,
begin
induction l with y ys ih,
    {
      unfold empty_list at h, contradiction
    },
    {
      unfold max_element foldr1,
      cases ys,
        {
          dsimp, apply h₁, left, refl
        },
        {
          have ih := ih _ _,
          unfold max_element foldr1 at ih,
          rw foldr_swap max ⟨max_comm⟩ ⟨max_assoc⟩,
          dsimp at *,
          rw max_le_iff,
          split,
            {
              apply h₁, left, refl
            },
            {
              exact ih_1
            },
          unfold empty_list, intros ok, cases ok,
          intros, apply h₁, right, simp [(∈)] at a, exact a
        }
    }
end

lemma min_le_max {α : Type*} [decidable_linear_order α] (a : α) {b c : α}
  (H : b ≤ c) : min a b ≤ max a c :=
begin
  unfold min max,
  by_cases h : a ≤ b; simp [h];
    by_cases h₁ : a ≤ c; simp [h₁],
  exact H, rw not_le at h, exact le_of_lt h
end

lemma min_elem_le_max_elem {α : Type*} [decidable_linear_order α] (l : list α)
  (h : ¬empty_list l) : min_element l h ≤ max_element l h :=
begin
  unfold min_element max_element,
  cases l with x xs, unfold empty_list at h, contradiction,
  unfold foldr1,
  induction xs with y ys,
    {dsimp, refl},
    {
      dsimp, 
      have h₁ : ¬empty_list (x :: ys),
        by unfold empty_list; intros; contradiction,
      have ih := xs_ih h₁,
      exact min_le_max y ih
    }
end

lemma map_empty_iff_l_empty {α β : Type} (f : α → β) (l : list α) :
  empty_list (map f l) ↔ empty_list l :=
begin
  split; intros h; cases l; try {finish <|> simp [empty_list]}
end

lemma unzip_one {α β : Type} (l : α) (r : β) (xs : list (α × β)) :
  unzip ((l, r) :: xs) = ((l :: (unzip xs).fst), r :: (unzip xs).snd) :=
begin
  simp [unzip],
  cases (unzip xs),
  simp [unzip]
end

lemma unzip_fst_empty_iff_l_empty {α β : Type} (l : list (α × β)) :
  empty_list ((unzip l).fst) ↔ empty_list l :=
begin
  split; intros h; cases l; try {finish};
  simp [empty_list, unzip] at *,
  cases l_hd,
  rw unzip_one at h,
  contradiction
end

lemma unzip_snd_empty_iff_l_empty {α β : Type} (l : list (α × β)) :
  empty_list ((unzip l).snd) ↔ empty_list l :=
begin
  split; intros h; cases l; try {finish};
  simp [empty_list, unzip] at *,
  cases l_hd,
  rw unzip_one at h,
  contradiction
end

lemma pair_in_zip_l {α β} {a b} {l₁ : list α} {l₂ : list β}
  (h : (a, b) ∈ zip l₁ l₂) : a ∈ l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {
      simp [zip, zip_with] at h, contradiction
    },
    {
      cases l₂ with y ys,
        {
          simp [zip, zip_with] at h,
          contradiction
        },
        {
          unfold1 zip at h,
          unfold1 zip_with at h,
          rw mem_cons_iff at h,
          cases h, injection h with hl hr,
          subst hl, subst hr,
          left, refl, rw mem_cons_eq,
          right, apply ih, 
          unfold zip, exact h
        }
    }
end

lemma pair_in_zip_r {α β} {a b} {l₁ : list α} {l₂ : list β}
  (h : (a, b) ∈ zip l₁ l₂) : b ∈ l₂ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {
      simp [zip, zip_with] at h, contradiction
    },
    {
      cases l₂ with y ys,
        {
          simp [zip, zip_with] at h,
          contradiction
        },
        {
          unfold1 zip at h,
          unfold1 zip_with at h,
          rw mem_cons_iff at h,
          cases h, injection h with hl hr,
          subst hl, subst hr,
          left, refl, rw mem_cons_eq,
          right, apply ih, 
          unfold zip, exact h
        }
    }
end

def decidable_uncurry {α β : Type*} {f : α → β → Prop} {x : α × β}
  (h : decidable (f x.fst x.snd)) : decidable (uncurry f x) :=
begin
  resetI,
  cases x, unfold_projs at *,
  simp [uncurry],
  exact h
end

lemma filter_forall {α : Type*} {P : α → Prop} [decidable_pred P] (xs : list α)
  (x : α) (h₁ : x ∈ filter P xs) : P x :=
begin
  induction xs with x₁ xs₁ ih; simp [filter] at h₁,
    {
      contradiction
    },
    {
      by_cases h₂ : (P x₁); simp [h₂] at h₁,
        {cases h₁,
           {cc},
           {exact ih h₁}},
        {exact ih h₁}
    }
end

lemma unempty_filter_ex {α : Type*} {xs : list α} {p : α → Prop}
  [decidable_pred p] (h : ¬empty_list (filter p xs)) :
  ∃x, x ∈ xs ∧ p x :=
begin
  induction xs with x₁ xs₁ ih,
    {
      dsimp at h, unfold empty_list at h, contradiction
    },
    {
      by_cases h₁ : p x₁,
        {
          existsi x₁, finish
        },
        {
          unfold empty_list at *,
          unfold filter at h,
          simp [h₁] at h,
          have ih := ih h,
          cases ih with x₂ px₂,
          existsi x₂,
          simp [(∈), list.mem] at *,
          split, right, exact px₂.left,
          exact px₂.right
        }
    }
end

def conv {α : Type*} (f : α → Type*) {a b : α} : a = b → f a → f b :=
  assume h₁ h₂, by rw ← h₁; exact h₂

def list_iso {α : Type*} [decidable_eq α] : list α → list α → bool
  | []        []        := tt
  | (x :: xs) (y :: ys) := band (x = y) (list_iso xs ys)
  | _         _         := ff

lemma list_iso_refl {α : Type*} [decidable_eq α] (l : list α) :
  list_iso l l :=
begin
  induction l; simp [list_iso], assumption
end

lemma list_iso_nil_l {α : Type*} [decidable_eq α] (l : list α)
  : list_iso nil l ↔ l = nil :=
  iff.intro
    (λh, begin cases l with x xs, refl, simp [list_iso] at h, contradiction end)
    (λh, begin cases l with x xs, exact list_iso_refl _, cases h end)

lemma list_iso_nil_r {α : Type*} [decidable_eq α] (l : list α)
  : list_iso l nil ↔ l = nil :=
  iff.intro
    (λh, begin cases l with x xs, refl, simp [list_iso] at h, contradiction end)
    (λh, begin cases l with x xs, exact list_iso_refl _, cases h end)

lemma list_iso_symm {α : Type*} [decidable_eq α] {l₁ l₂ : list α}
  (h : list_iso l₁ l₂) : list_iso l₂ l₁ :=
begin
  induction l₁ with x xs generalizing l₂; cases l₂ with y ys; try {assumption},
  simp [list_iso], simp [list_iso] at h,
  cases h with h₁ h₂,
  rw and_iff_left, exact eq.symm h₁,
  apply l₁_ih, exact h₂
end

lemma list_iso_trans {α : Type*} [decidable_eq α] {l₁ l₂ l₃ : list α}
  (h : list_iso l₁ l₂) (h₁ : list_iso l₂ l₃) : list_iso l₁ l₃ :=
begin
  induction l₁ with x xs ih generalizing l₂ l₃; cases l₃ with y ys,
    {exact list_iso_refl _},
    {
      rw list_iso_nil_l at h, rw h at h₁,
      rw list_iso_nil_l at h₁, cases h₁
    },
    {
      rw list_iso_nil_r at h₁, rw h₁ at h,
      exact h
    },
    {
      simp [list_iso],
      cases l₂ with z zs,
        {
          rw list_iso_nil_r at h, cases h
        },
        {
          simp [list_iso] at h h₁,
          cases h₁, cases h, split, cc,
          apply ih, exact h_right, exact h₁_right
        }
    }
end

lemma list_iso_hd {α : Type*} [decidable_eq α] {x} {y} {xs ys : list α}
  (h : list_iso (x :: xs) (y :: ys)) : x = y :=
begin
  simp [list_iso] at h,
  exact h.left
end

lemma list_iso_tl {α : Type*} [decidable_eq α] {x} {y} {xs ys : list α}
  (h : list_iso (x :: xs) (y :: ys)) : list_iso xs ys :=
begin
  simp [list_iso] at h,
  exact h.right
end

lemma list_iso_iff {α : Type*} [decidable_eq α] {l₁ l₂ : list α} :
  list_iso l₁ l₂ ↔ l₁ = l₂ :=
begin
  split; intros h,
    {
      induction l₁ with x xs ih generalizing l₂,
        {
          cases l₂ with y ys,
            {refl},
            {rw list_iso_nil_l at h, cases h}
        },
        {
          cases l₂ with y ys, 
            {rw list_iso_nil_r at h, cases h},
            {
              have h₁ : x = y, from list_iso_hd h,
              congr, exact h₁, apply ih,
              apply list_iso_tl h
            }
        }
    },
    {
      rw h, exact list_iso_refl _
    }
end

def mod_self {n : ℕ} : n % n = 0 :=
begin
  induction n with n ih, refl,
  rw nat.mod_def,
  rw if_pos,
  rw nat.sub_self,
  rw nat.zero_mod,
  split, rw succ_eq_add_one, rw add_comm,
  exact zero_lt_one_add _, refl
end

lemma repeat_bounded {α : Type*} {a : α} {b} :
  ∀{x}, x ∈ list.repeat a b → x = a :=
assume x h,
begin
  induction b with b ih,
    {
      cases h
    },
    {
      simp at h, cases h, assumption,
      exact ih h
    }
end

end utils