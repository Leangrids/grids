import utils
import data.vector data.list

open utils

section grids

class relative_grid (α : Type*) :=
  (carrier : Type)
  (rows    : α → ℕ)
  (cols    : α → ℕ)
  (unempty : Πg, rows g * cols g > 0)
  (data    : Πg, bounded 0 (rows g) → bounded 0 (cols g) → carrier)

class grid (α : Type*) extends relative_grid α :=
  (bottom_left : α → point)

variables {α : Type*} [grid α] (g : α)

open grid relative_grid

def size := rows g * cols g

def gsize := @size α

def top_right (bottom_left : point) (r c : ℕ) : point :=
  ⟨bottom_left.x + c, bottom_left.y - r⟩

def top_right' (bottom_left : point) {α : Type*} [relative_grid α] (g : α) :=
  top_right bottom_left (rows g) (cols g)

lemma linear_bounds {a b : ℤ} {c : ℕ} (h₁ : a < b) (h₂ : b - ↑c ≤ a) :
  int.nat_abs(a + ↑c - b) < c :=
begin
  rw [← sub_nonneg, ← sub_add, sub_add_eq_add_sub] at h₂,
  rw [
    ← int.coe_nat_lt, int.nat_abs_of_nonneg h₂,
    sub_lt_iff_lt_add', add_lt_add_iff_right
  ], exact h₁
end

structure bounding_box := (p₁ : point) (p₂ : point) (h : p₁ ↗ p₂)

def bound_box_str : bounding_box → string
  | ⟨p₁, p₂, _⟩ := "<(" ++ to_string p₁ ++ ", " ++ to_string p₂ ++ ")>"

instance : has_to_string bounding_box := ⟨bound_box_str⟩

instance : has_repr bounding_box := ⟨bound_box_str⟩

def points_of_box (bb : bounding_box) : point × point := ⟨bb.p₁, bb.p₂⟩

def rows_of_box : bounding_box → ℕ
  | ⟨⟨_, y₁⟩, ⟨_, y₂⟩, _⟩ := int.nat_abs (y₁ - y₂)

def cols_of_box : bounding_box → ℕ
  | ⟨⟨x₁, _⟩, ⟨x₂, _⟩, _⟩ := int.nat_abs (x₂ - x₁)

def rows_of_box_pos {bb : bounding_box} : rows_of_box bb > 0 :=
let ⟨⟨_, y₁⟩, ⟨_, y₂⟩, h⟩ := bb in
begin
  simp only [rows_of_box],
  simp [(↗)] at h,
  simp only [(>)],
  rw ← int.coe_nat_lt_coe_nat_iff,
  rw int.nat_abs_of_nonneg,
  rw lt_sub_iff, simp, exact h.right,
  simp only [(≥)], 
  apply le_of_lt, 
  rw lt_sub_iff, simp, exact h.right
end

def cols_of_box_pos {bb : bounding_box} : cols_of_box bb > 0 :=
let ⟨⟨x₁, _⟩, ⟨x₂, _⟩, h⟩ := bb in
begin
  simp only [cols_of_box],
  simp [(↗)] at h,
  simp only [(>)],
  rw ← int.coe_nat_lt_coe_nat_iff,
  rw int.nat_abs_of_nonneg,
  rw lt_sub_iff, simp, exact h.left,
  simp only [(≥)], 
  apply le_of_lt, 
  rw lt_sub_iff, simp, exact h.left
end

attribute [simp]
def grid_rows := rows g

attribute [simp]
def grid_cols := cols g

attribute [simp]
def grid_bottom_left := bottom_left g

attribute [simp]
def grid_top_right := top_right (bottom_left g) (rows g) (cols g)

def rows_cols_bounded {rows cols : ℕ} (h₁ : rows > 0) (h₂ : cols > 0)
  (o : point) : o↗{x := o.x + ↑cols, y := o.y - ↑rows} :=
  begin
    cases o, simp [(↗)],
    exact and.intro h₂ (sub_lt_self _ begin simp [(>)], exact h₁ end)
  end

def grid_bounding_boxes :
  bottom_left g ↗ grid_top_right g :=
begin
  simp [grid_bounded_iff, (↗), top_right, grid.bottom_left],
  have h := gt_both_of_mult (relative_grid.unempty g),
  exact and.intro h.right (sub_lt_self _ (by simp [(>)]; exact h.left))
end

def bbox_of_grid (g : α) : bounding_box :=
  ⟨bottom_left g, grid_top_right g, grid_bounding_boxes g⟩

structure relative_point :=
  (x : bounded 0 (rows g))
  (y : bounded 0 (cols g))

def relative_point_str : relative_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

instance has_to_string_rp : has_to_string (relative_point g) :=
  ⟨relative_point_str g⟩ 

instance has_repr_rp : has_repr (relative_point g) :=
  ⟨relative_point_str g⟩ 

structure grid_point :=
  (x : bounded ((grid_top_right g).y) ((bottom_left g).y))
  (y : bounded ((bottom_left g).x) ((grid_top_right g).x))

def grid_point_str : grid_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "] - " ++
             to_string (bottom_left g)

instance has_to_string_gp : has_to_string (grid_point g) := ⟨grid_point_str g⟩ 

instance has_repr_gp : has_repr (grid_point g) := ⟨grid_point_str g⟩ 

def apoint_of_gpoint {g : α} : grid_point g → relative_point g
  | ⟨⟨x, ⟨lbx, ubx⟩⟩, ⟨y, ⟨lby, uby⟩⟩⟩ :=
    let top_left_x := (bottom_left g).x in 
    let top_left_y := (bottom_left g).y - rows g in ⟨
      ⟨int.nat_abs (x - top_left_y),
        have h : x - top_left_y ≥ 0,
          from iff.elim_right le_sub_iff_add_le
            begin
              simp [grid_top_right, top_right] at lbx,
              simp [top_left_y],
              exact lbx
            end,
          and.intro
            (int.le_of_coe_nat_le_coe_nat $
             eq.symm (int.nat_abs_of_nonneg h) ▸ h)
            (iff.elim_left (int.coe_nat_lt_coe_nat_iff _ _) $
             eq.symm (int.nat_abs_of_nonneg h) ▸
             begin
               simp only [top_left_y], rw ← sub_add,
               rw ← zero_add (↑(rows g)), conv { to_lhs, simp only [zero_add]},
               rw add_lt_add_iff_right,
               rw sub_lt_iff,
               simp,
               exact ubx
             end)⟩,
      ⟨int.nat_abs (y - top_left_x),
        have h : y - top_left_x ≥ 0,
          from iff.elim_right le_sub_iff_add_le
            begin
              simp [top_left_y],
              exact lby
            end,
        and.intro
          (int.le_of_coe_nat_le_coe_nat $
           eq.symm (int.nat_abs_of_nonneg h) ▸ h)
          (iff.elim_left (int.coe_nat_lt_coe_nat_iff _ _) $
           eq.symm (int.nat_abs_of_nonneg h) ▸
           begin
             simp only [top_left_x], 
             simp only [grid_top_right, top_right] at uby,
             rw sub_lt_iff,
             rw add_comm,
             exact uby
           end
          )⟩
    ⟩

def gpoint_of_apoint {g : α} : relative_point g → grid_point g
  | ⟨⟨x, ⟨lbx, ubx⟩⟩, ⟨y, ⟨lby, uby⟩⟩⟩ :=
    let top_left_x := (bottom_left g).x in
    let top_left_y := (bottom_left g).y - rows g in ⟨
      ⟨top_left_y + x,
       and.intro
        (by simp [top_left_y, top_right])
        begin
          simp [top_left_y, top_right],
          conv { to_rhs, rw ← add_zero (bottom_left g).y},
          rw add_lt_add_iff_left, rw ← sub_eq_add_neg,
          rw sub_lt_iff, simp, 
          rw int.coe_nat_lt, exact ubx
        end⟩,
      ⟨top_left_x + y,
       and.intro
        (by simp [top_left_x])
        begin
          simp [top_left_x, grid_top_right, top_right],
          rw int.coe_nat_lt, exact uby
        end⟩
    ⟩

def prod_of_rel_point {g : α} (rp : relative_point g) := (rp.x, rp.y)

def prod_of_grid_point {g : α} (ap : grid_point g) := (ap.x, ap.y)

def grid_point_of_prod {g : α}
  (p : bounded ((bottom_left g).x) ((grid_top_right g).x) ×
       bounded ((grid_top_right g).y) ((bottom_left g).y)) : grid_point g :=
  ⟨p.snd, p.fst⟩

def grid_point_of_prod' {g : α}
  (p : bounded ((grid_top_right g).y) ((bottom_left g).y) ×
       bounded ((bottom_left g).x) ((grid_top_right g).x)) : grid_point g :=
  ⟨p.fst, p.snd⟩

def abs_data (g : α) :=
  (function.uncurry (data g)) ∘ prod_of_rel_point ∘ apoint_of_gpoint

lemma grid_rows_eq_bly_sub_try :
  grid_rows g = int.nat_abs ((bottom_left g).y - (grid_top_right g).y) :=
begin
  unfold grid_rows grid_top_right top_right,
  dsimp,
  repeat {rw ← sub_eq_add_neg},
  rw [← sub_add, sub_self, zero_add],
  refl
end

lemma grid_cols_eq_trx_sub_blx 
  : grid_cols g = int.nat_abs ((grid_top_right g).x - (bottom_left g).x) :=
begin
  unfold grid_cols grid_top_right top_right,
  dsimp,
  rw [← sub_eq_add_neg, add_comm, add_sub_cancel],
  refl
end

lemma bounded_establishes_bounds {a b : ℤ}
  (h : a < b) (x : bounded 0 (int.nat_abs (b - a))) :
  a ≤ a + ↑x ∧ a + ↑x < b :=
have xpos : ↑x ≥ 0, from positive_bounded _,
have xmax : ↑x < int.nat_abs (b - a), from bounded_lt _,
and.intro begin
            apply le_add_of_nonneg_right,
            unfold coe at *
          end
          begin
            rw [add_comm, ← lt_sub_iff],
            unfold_coes at *,
            rw [← int.coe_nat_lt, int.nat_abs_of_nonneg] at xmax,
            exact xmax,
            simp [(≥)],
            rw [
              ← sub_eq_add_neg, ← add_le_add_iff_right a,
              zero_add, sub_add_cancel
            ],
            apply int.le_of_lt,
            exact h
          end

end grids

section grid_impls

structure grid₀ (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (data : vector α (r * c))

structure agrid₀ (α : Type) extends grid₀ α :=
  (o : point)

structure fgrid (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (o : point)
  (data : bounded (o.y - r) o.y → bounded o.x (o.x + c) → α)

end grid_impls

section grid_instances

lemma linearize_array {x y r c : ℕ}
  (xb : is_bounded 0 c x) (yb : is_bounded 0 r y) : y * c + x < r * c :=
let ⟨xl, xu⟩ := xb in
let ⟨yl, yu⟩ := yb in
have rows_pos : 0 < r, from lt_of_le_of_lt yl yu,
have cols_pos : 0 < c, from lt_of_le_of_lt xl xu,
have h₁ : y * c < r * c,
  from mul_lt_mul yu (le_refl _) cols_pos (le_of_lt rows_pos),
have h₂ : ∃n, nat.succ y + n = r, from nat_le_dest yu,
let ⟨n, h₂⟩ := h₂ in
by rw [← h₂, right_distrib, nat.succ_mul, add_assoc];
   exact add_lt_add_of_le_of_lt (le_refl _)
         (@nat.lt_add_right _ _ _ xu)

instance rg_grid₀ {α : Type} :
  relative_grid (grid₀ α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λg, g.h,
    data    :=
    λg ⟨y, ⟨yl, yu⟩⟩ ⟨x, ⟨xl, xu⟩⟩,
      g.data.nth ⟨
        y * g.c + x,
        linearize_array (is_bounded_of_bounds xl xu)
                        (is_bounded_of_bounds yl yu)
      ⟩    
}

instance rg_agrid₀ {α : Type} :
  relative_grid (agrid₀ α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λ⟨⟨_, _, p, _⟩, _⟩, p,
    data    :=
    λg ⟨y, ⟨yl, yu⟩⟩ ⟨x, ⟨xl, xu⟩⟩,
      g.data.nth ⟨
        y * g.c + x,
        linearize_array (is_bounded_of_bounds xl xu)
                        (is_bounded_of_bounds yl yu)
      ⟩   
}

lemma absolute_bounds (o : ℤ) (r : ℕ) (x : bounded 0 r) : o - ↑r + ↑x < o :=
begin
  simp, conv {to_rhs, rw ← add_zero o},
  rw add_lt_add_iff_left, apply add_lt_of_lt_sub_right,
  rw zero_sub, apply neg_lt_neg,
  cases x, rw ← coe_is_z_of_bounded,
  simp [z_of_bounded],
  rw int.coe_nat_lt, exact x_property.right
end

instance rg_fgrid {α : Type} :
  relative_grid (fgrid α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λg, g.h,
    data    := λg x y,
    g.data ⟨g.o.y - ↑g.r + x,
            and.intro (le_add_of_nonneg_right $ by cases x; unfold_coes)
                      (absolute_bounds g.o.y g.r x)⟩
           ⟨g.o.x + y,
            and.intro (le_add_of_nonneg_right $ by cases x; unfold_coes)
                      (add_lt_add_left (
                        let ⟨y, ⟨_, h⟩⟩ := y in
                        iff.elim_right int.coe_nat_lt h) g.o.x)⟩
}

instance ag_agrid₀ {α : Type} :
  grid (agrid₀ α) := {
    bottom_left := λg, g.o
  }

instance ag_f {α : Type} :
  grid (fgrid α) := {
    bottom_left := λg, g.o
  }

def point_of_grid_point {α : Type*} [grid α] (g : α) : grid_point g → point
  | ⟨b₁, b₂⟩ := ⟨b₁, b₂⟩

instance point_grid_point_coe {α : Type*} [grid α] (g : α) :
  has_coe (grid_point g) point := ⟨point_of_grid_point g⟩

end grid_instances

section finite_grid

open list int

notation `[|`:max x `|]`:0 := nat_abs x

variables {α : Type*} [grid α] (g : α)

def grid_row {c d : ℤ} (a b : ℤ) (row : bounded c d)
  : list (bounded a b × bounded c d) :=
  zip (range a b) (repeat row [|b - a|])

def grid_row_pure (a b row : ℤ) : list point :=
  map (function.uncurry point.mk) $ zip (range_pure a b) (repeat row [|b - a|])
  
lemma grid_row_pure_bounds {a b row : ℤ} :
  ∀{c : point}, c ∈ grid_row_pure a b row →
    is_bounded a b c.x ∧ is_bounded row (row + 1) c.y :=
assume c h,
begin
  simp [grid_row_pure] at h,
  cases h with a₁ h₁,
  cases h₁ with b₁ h₂,
  cases h₂ with h₂ h₃,
  have h₄ : a₁ ∈ range_pure a b, from pair_in_zip_l h₂,
  have h₅ : b₁ ∈ repeat row [|b + -a|], from pair_in_zip_r h₂,
  split; split,
    {
      rw ← h₃,
      have h₆ : (function.uncurry point.mk (a₁, b₁)).x = a₁,
        by simp [function.uncurry], rw h₆,
      have h₇ : is_bounded a b a₁, from range_pure_bounded h₄,
      cases h₇ with h₇ _,
      exact h₇
    },
    {
      rw ← h₃,
      have h₆ : (function.uncurry point.mk (a₁, b₁)).x = a₁,
        by simp [function.uncurry], rw h₆,
      have h₇ : is_bounded a b a₁, from range_pure_bounded h₄,
      cases h₇ with _ h₇,
      exact h₇
    },
    {
      rw ← h₃,
      have h₆ : (function.uncurry point.mk (a₁, b₁)).y = b₁,
        by simp [function.uncurry], rw h₆,
      have h₇ : b₁ = row, from repeat_bounded h₅,
      rw h₇
    },
    {
      rw ← h₃,
      have h₆ : (function.uncurry point.mk (a₁, b₁)).y = b₁,
        by simp [function.uncurry], rw h₆,
      have h₇ : b₁ = row, from repeat_bounded h₅,
      rw h₇,
      exact lt_add_succ _ _
    }
end

lemma grid_row_empty_iff {c d : ℤ} (a b : ℤ) (row : bounded c d) :
  grid_row a b row = [] ↔ b ≤ a :=
by unfold grid_row; exact
iff.intro
  (λh, begin
         rw zip_nil_iff at h,
         cases h,
           {rw range_empty_iff at h, exact h},
           {rw repeat_nil at h,
            rw nat_abs_zero_iff at h,
            finish}
       end)
  (λh, have h₁ : range a b = [],
         from iff.elim_right (range_empty_iff _ _) h,   
       by rw h₁; refl)

lemma grid_row_length {c d : ℤ} {a b : ℤ} (h : a < b) {x : bounded c d} :
  length (grid_row a b x) = nat_abs (b - a) :=
begin
  unfold grid_row,
  rw length_zip_left,
  exact range_length (int.le_of_lt h),
  rw length_repeat,
  exact range_length (int.le_of_lt h)
end

lemma grid_row_pure_length {a b : ℤ} (h : a < b) {x : ℤ} :
  length (grid_row_pure a b x) = nat_abs (b - a) :=
begin
  unfold grid_row_pure,
  rw length_map,
  rw length_zip_left,
  exact range_length_pure (int.le_of_lt h),
  rw length_repeat,
  exact range_length_pure (int.le_of_lt h)
end

def grid_indices (p₁ p₂ : point) : list (bounded p₁.x p₂.x × bounded p₂.y p₁.y)
  := join (map (grid_row p₁.x p₂.x) (range p₂.y p₁.y))

def grid_indices_pure (p₁ p₂ : point) : list point :=
  join (map (grid_row_pure p₁.x p₂.x) (range_pure p₂.y p₁.y))

open relative_grid grid

def grid_indices_g := grid_indices (bottom_left g) (grid_top_right g)

def grid_indices_g_pure := grid_indices_pure (bottom_left g) (grid_top_right g)

def is_in_grid' (xy : point) :=
  is_bounded (grid_top_right g).y (grid_bottom_left g).y xy.y ∧
  is_bounded (grid_bottom_left g).x (grid_top_right g).x xy.x

def is_in_grid (bb : bounding_box) (xy : point) :=
  is_bounded bb.p₂.y bb.p₁.y xy.y ∧ is_bounded bb.p₁.x bb.p₂.x xy.x

lemma grid_indices_pure_in_grid {p₁ p₂ : point} {h : p₁ ↗ p₂} :
  ∀{a}, a ∈ grid_indices_pure p₁ p₂ → is_in_grid ⟨p₁, p₂, h⟩ a :=
assume a h,
begin
  cases a with al ar,
  simp [grid_indices_pure] at h,
  cases h with l h, cases h with h h₁,
  cases h with a₁ h₂, cases h₂ with h₂ h₃,
  have h₄ := range_pure_bounded h₂,
  rw ← h₃ at h₁,
  have h₅ := grid_row_pure_bounds h₁,
  split; split,
    {
      simp [bounding_box.p₁],
      cases h₅ with h₅l h₅r,
      cases h₅l with h₅l₁ h₅l₂,
      cases h₅r with h₅r₁ h₅r₂,
      simp [point.x, point.y] at *,
      cases h₄ with h₄l h₄r, 
      transitivity a₁; assumption
    },
    {
      have h₄ := range_pure_bounded h₂, 
      exact lt_of_le_of_lt (le_of_lt_add_one h₅.right.right) h₄.right
    },
    {exact h₅.left.left},
    {exact h₅.left.right}
end

def grid_indices_g_pure_in_grid {g : α} :
  ∀{a}, a ∈ grid_indices_g_pure g → is_in_grid (bbox_of_grid g) a :=
assume a h, grid_indices_pure_in_grid h

def decide_grid :=
  map (abs_data g ∘ grid_point_of_prod) (grid_indices_g g)

lemma attach_length {α : Type} {l : list α} :
  length (list.attach l) = length l := 
begin
  induction l with x xs ih,
    {
      refl
    },
    {
      simp [attach]
    }
end

def make_bounded_idx {g : α} (p : point) (h : is_in_grid (bbox_of_grid g) p) :
  bounded ((bottom_left g).x) ((grid_top_right g).x) ×
  bounded ((grid_top_right g).y) ((bottom_left g).y) :=
    (make_bounded h.right, make_bounded h.left)

def make_bounded_indices (is : list point)
                         (h : ∀p, p ∈ is → is_in_grid (bbox_of_grid g) p) :
  list (
    bounded ((bottom_left g).x) ((grid_top_right g).x) ×
    bounded ((grid_top_right g).y) ((bottom_left g).y)
  ) := map (λp : {x // x ∈ is},
         (⟨p.val.x, (h p.val p.property).right⟩,
          ⟨p.val.y, (h p.val p.property).left⟩)) (attach is)

def decide_grid_pure :=
  map (abs_data g ∘ grid_point_of_prod ∘
       (λidx : {x // x ∈ grid_indices_g_pure g},
          make_bounded_idx idx.val (grid_indices_g_pure_in_grid idx.property)))
          (attach $ grid_indices_g_pure g)

lemma grid_indices_ignores_data {α : Type*} [grid α] {g : α} :
  grid_indices_g g = grid_indices (grid_bottom_left g) (grid_top_right g) := rfl

def fgrid_iso_grid [decidable_eq (carrier α)] (g₁ g₂ : α) : bool :=
    rows g₁ = rows g₂ ∧ cols g₁ = cols g₂ ∧ bottom_left g₁ = bottom_left g₂ ∧
    let l₁ := decide_grid g₁ in
    let l₂ := decide_grid g₂ in
    if list_iso l₁ l₂ then tt else ff

infix `~ₘ`:100 := fgrid_iso_grid

instance gdec [decidable_eq (carrier α)] (g₁ g₂ : α) : decidable (g₁ ~ₘ g₂) :=
  by apply_instance

lemma fgrid_iso_refl [decidable_eq (carrier α)] : g ~ₘ g :=
  by simp [fgrid_iso_grid, list_iso_refl]

lemma fgrid_iso_symm [decidable_eq (carrier α)] {g₁ g₂ : α}
  (h : g₁ ~ₘ g₂) : g₂ ~ₘ g₁ :=
begin
  simp [fgrid_iso_grid] at h, simp [fgrid_iso_grid],
  split; try {split},
    {exact eq.symm h.left},
    {exact eq.symm h.right.left},
    {split, exact eq.symm h.right.right.left,
            apply list_iso_symm, exact h.right.right.right}
end

lemma fgrid_iso_trans [decidable_eq (carrier α)] {g₁ g₂ g₃ : α}
  (h : g₁ ~ₘ g₂) (h₁ : g₂ ~ₘ g₃) : g₁ ~ₘ g₃ :=
begin
  simp [fgrid_iso_grid], simp [fgrid_iso_grid] at h h₁,
  split; try {split},
    {cc},
    {transitivity cols g₂, exact h.right.left, exact h₁.right.left},
    {split, transitivity bottom_left g₂, exact h.right.right.left,
     exact h₁.right.right.left,
     exact list_iso_trans h.right.right.right h₁.right.right.right}
end

lemma caut_iso_size [decidable_eq (carrier α)] {g₁ g₂ : α}
  (h : g₁ ~ₘ g₂) : gsize g₁ = gsize g₂ :=
begin
  simp [fgrid_iso_grid] at h,
  by_cases h₁ : rows g₁ = rows g₂;
  by_cases h₂ : cols g₁ = cols g₂; try {cc},
    {unfold gsize size relative_grid.rows relative_grid.cols, cc}
end

section grid_instances

instance fgrid_functor : functor fgrid := {
  map := λα β f g, ⟨g.r, g.c, g.h, g.o, λx y, f (g.data x y)⟩
}

end grid_instances

def point_of_bounded_prod {a b c d : ℤ} : bounded a b × bounded c d → point
  | ⟨⟨a, _⟩, ⟨c, _⟩⟩ := ⟨a, c⟩

lemma grid_indices_bad_horizontal {p₁ p₂ : point}
  (h : p₂.x ≤ p₁.x) : grid_indices p₁ p₂ = [] :=
begin
  unfold grid_indices, 
  cases p₁, cases p₂,
  unfold_projs at *,
  apply join_empty_of_all_empty,
  intros x h₁,
  rw list.mem_map at h₁,
  cases h₁, cases h₁_h,
  rw [← h₁_h_right, grid_row_empty_iff],
  exact h
end

lemma grid_indices_bad_vertical {p₁ p₂ : point}
  (h : p₁.y ≤ p₂.y) : grid_indices p₁ p₂ = [] :=
begin
  unfold grid_indices, 
  cases p₁, cases p₂,
  unfold_projs at *,
  have h₁ : range p₂_y p₁_y = [],
    from iff.elim_right (range_empty_iff _ _) h,
  rw h₁, refl
end

-- This takes forever to typecheck due to generalize
-- lemma range_ex {a b : ℤ} (h : a < b) :
--   range a b = ⟨a, and.intro (le_refl _) h⟩ ::
--               list.map range_weaken (range (a + 1) b) :=
-- begin
--   generalize hack : range (a + 1) b = l,
--   unfold1 utils.range, simp [h],
--   rw ← hack
-- end

lemma range_ex {a b : ℤ} (h : a < b) : ∀l, range (a + 1) b = l → 
  range a b = ⟨a, and.intro (le_refl _) h⟩ ::
              list.map range_weaken l :=
assume l hack,
begin
  unfold1 utils.range,
  rw [dif_pos h, ← hack]
end

lemma grid_indices_bad_iff (p₁ p₂ : point) :
  grid_indices p₁ p₂ = [] ↔ ¬p₁ ↗ p₂ :=
iff.intro (λh, begin
                 intros contra,
                 cases p₁; cases p₂,
                 simp [(↗)] at contra,
                 cases contra with l r,
                 unfold grid_indices at h,
                 dsimp at h,
                 revert h,
                 rw range_ex r (range (p₂_y + 1) p₁_y) rfl,
                 unfold map join grid_row,
                 rw range_ex l (range (p₁_x + 1) p₂_x) rfl,
                 have h₂ : nat_abs (p₂_x - p₁_x) ≥ 1,
                   from nat_abs_of_lt l,
                 rw repeat_more, unfold zip zip_with,
                 intros contra, cases contra, exact h₂ 
               end
          )
          (λh, begin
                 rw not_grid_bounded_iff at h,
                 cases h, exact grid_indices_bad_horizontal h,
                 exact grid_indices_bad_vertical h
               end
          )

lemma grid_indices_length {p₁ p₂ : point} (h : p₁ ↗ p₂) :
  length (grid_indices p₁ p₂) = [|p₁.y - p₂.y|] * [|p₂.x - p₁.x|] :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← nat_abs_mul],
  rw grid_bounded_iff at h,
  have h₁ : (p₁.y - p₂.y) * (p₂.x - p₁.x) > 0, from
    mul_pos begin
              simp [(>)],
              rw ← add_lt_add_iff_right p₂.y,
              rw zero_add, simp, exact h.right
            end
            begin
              simp [(>)],
              rw ← add_lt_add_iff_right p₁.x,
              rw zero_add, simp, exact h.left
            end,
  rw nat_abs_of_nonneg (int.le_of_lt h₁),
  unfold grid_indices,
  rw [length_join, map_map],
  simp [(∘)],
  simp [grid_row_length h.left ],
  rw range_length (int.le_of_lt h.right),
  repeat {rw ← sub_eq_add_neg},
  repeat {rw nat_abs_of_nonneg},
  rw mul_comm,
  simp [(≥)],
  rw [
    ← sub_eq_add_neg,
    ← add_le_add_iff_right p₂.y,
    zero_add, sub_add_cancel
  ], exact (int.le_of_lt h.right),
  simp [(≥)],
  rw [
    ← sub_eq_add_neg,
    ← add_le_add_iff_right p₁.x,
    zero_add,
    sub_add_cancel
  ],
  exact (int.le_of_lt h.left)
end

lemma grid_indices_pure_length {p₁ p₂ : point} (h : p₁ ↗ p₂) :
  length (grid_indices_pure p₁ p₂) = [|p₁.y - p₂.y|] * [|p₂.x - p₁.x|] :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← nat_abs_mul],
  rw grid_bounded_iff at h,
  have h₁ : (p₁.y - p₂.y) * (p₂.x - p₁.x) > 0, from
    mul_pos begin
              simp [(>)],
              rw ← add_lt_add_iff_right p₂.y,
              rw zero_add, simp, exact h.right
            end
            begin
              simp [(>)],
              rw ← add_lt_add_iff_right p₁.x,
              rw zero_add, simp, exact h.left
            end,
  rw nat_abs_of_nonneg (int.le_of_lt h₁),
  unfold grid_indices_pure,
  rw [length_join, map_map],
  simp [(∘)],
  simp [grid_row_pure_length h.left],
  rw range_length_pure (int.le_of_lt h.right),
  repeat {rw ← sub_eq_add_neg},
  repeat {rw nat_abs_of_nonneg},
  rw mul_comm,
  simp [(≥)],
  rw [
    ← sub_eq_add_neg,
    ← add_le_add_iff_right p₂.y,
    zero_add, sub_add_cancel
  ], exact (int.le_of_lt h.right),
  simp [(≥)],
  rw [
    ← sub_eq_add_neg,
    ← add_le_add_iff_right p₁.x,
    zero_add,
    sub_add_cancel
  ],
  exact (int.le_of_lt h.left)
end

lemma grid_indices_len_g_pure :
  length (grid_indices_g_pure g) = 
  length (grid_indices_pure (bottom_left g) (grid_top_right g)) :=
  by simp [grid_indices_g_pure]

theorem decide_grid_length {α : Type*} [grid α] (g : α) :
  length (decide_grid g) = grid_rows g * grid_cols g :=
begin
  unfold decide_grid grid_indices_g,
  rw [
    length_map, 
    grid_rows_eq_bly_sub_try, grid_cols_eq_trx_sub_blx, grid_indices_length
  ],
  exact grid_bounding_boxes g
end

theorem decide_grid_pure_length {α : Type*} [grid α] (g : α) :
  length (decide_grid_pure g) = grid_rows g * grid_cols g :=
begin
  unfold decide_grid_pure grid_indices_g_pure,
  rw length_map,
  rw grid_rows_eq_bly_sub_try,
  rw grid_cols_eq_trx_sub_blx,
  rw attach_length,
  rw grid_indices_len_g_pure,
  rw grid_indices_pure_length,
  exact grid_bounding_boxes g
end

def agrid_of_fgrid {α : Type} (g : fgrid α) : agrid₀ α :=
    ⟨⟨g.r, g.c, g.h, ⟨decide_grid g, decide_grid_length g⟩⟩, g.o⟩

def fgrid_of_agrid {α : Type} (g : agrid₀ α) : fgrid α :=
  ⟨g.r, g.c, g.h, g.o, λx y, abs_data g ⟨x, y⟩⟩

instance f_a_coe {α : Type} : has_coe (fgrid α) (agrid₀ α) := ⟨agrid_of_fgrid⟩
instance a_f_coe {α : Type} : has_coe (agrid₀ α) (fgrid α) := ⟨fgrid_of_agrid⟩

def row (n : bounded 0 (relative_grid.rows g)) :
  (bounded 0 (relative_grid.cols g)) → relative_grid.carrier α :=
  relative_grid.data g n

def col (n : bounded 0 (relative_grid.cols g)) :
  (bounded 0 (relative_grid.rows g)) → relative_grid.carrier α :=
  flip (relative_grid.data g) n

def top :=
  row g ⟨0,
    and.intro (le_refl _)
              begin
                exact and.elim_left (gt_both_of_mult (relative_grid.unempty g))
              end⟩

def bot :=
  row g ⟨nat.pred (relative_grid.rows g),
         and.intro (nat.zero_le _)
                   begin
                     apply nat.pred_lt,
                     have c_unempty := relative_grid.unempty g,
                     unfold_projs,
                     cases relative_grid.rows g,
                     rw zero_mul at c_unempty,
                     have : ¬0 > 0, from gt_irrefl _,
                       contradiction,
                     trivial
                   end⟩

def left :=
  have h : relative_grid.cols g > 0,
    from and.elim_right (gt_both_of_mult (relative_grid.unempty g)),
  col g ⟨0, and.intro (le_refl _) h⟩

def right :=
  have h : relative_grid.cols g > 0,
    from and.elim_right (gt_both_of_mult (relative_grid.unempty g)),
  col g ⟨nat.pred (relative_grid.cols g),
         and.intro (nat.zero_le _)
                   begin
                     apply nat.pred_lt,
                     cases relative_grid.cols g,
                     have : ¬0 > 0, from gt_irrefl _,
                       contradiction,
                     trivial
                   end⟩

def grid_bounds' (h : relative_grid.rows g * relative_grid.cols g > 0)
  : bounding_box :=
  ⟨grid_bottom_left g, grid_top_right g,
   have h : _ := gt_both_of_mult h,
   rows_cols_bounded h.left h.right _⟩

def grid_bounds : bounding_box :=
  ⟨grid_bottom_left g, grid_top_right g,
     have h : _ := gt_both_of_mult (relative_grid.unempty g),
     rows_cols_bounded h.left h.right _⟩

instance decidable_is_in_grid' {xy : point}
   : decidable (is_in_grid' g xy) :=
   by simp [is_in_grid']; apply_instance

instance decidable_is_in_grid (bb : bounding_box) {xy : point}
   : decidable (is_in_grid bb xy) :=
   by simp [is_in_grid]; apply_instance

lemma is_in_grid_grid'_iff (xy : point) :
  is_in_grid' g xy ↔
  is_in_grid ⟨grid.bottom_left g,
              grid_top_right g,
              grid_bounding_boxes g⟩ xy :=
iff.intro (λh, and.intro h.left h.right)
          (λh, and.intro h.left h.right)

def overlaid_by (p₁ p₂ : bounding_box) :=
  (p₂.p₁.x ≤ p₁.p₁.x ∧ p₁.p₂.x ≤ p₂.p₂.x) ∧
  (p₂.p₂.y ≤ p₁.p₂.y ∧ p₁.p₁.y ≤ p₂.p₁.y)

def in_grid_bounded (p : point)
  (h : is_in_grid' g p) :=
  let ⟨left, right⟩ :=
    h in (make_bounded left, make_bounded right)

instance overlaid_decidable (p₁ p₂ : bounding_box) :
  decidable (overlaid_by p₁ p₂) := by simp [overlaid_by]; apply_instance

lemma overlaid_by_refl (p : bounding_box) : overlaid_by p p :=
  by simp [overlaid_by]; repeat {split}; refl

lemma overlaid_by_trans {p₁ p₂ p₃ : bounding_box}
  (h : overlaid_by p₁ p₂) (h₁ : overlaid_by p₂ p₃) : overlaid_by p₁ p₃ :=
begin
  simp [overlaid_by] at *; repeat {split}; transitivity,
  exact h₁.left.left, exact h.left.left,
  exact h.left.right, exact h₁.left.right,
  exact h₁.right.left, exact h.right.left,
  exact h.right.right, exact h₁.right.right
end

lemma overlaid_by_antisymm {p₁ p₂ : bounding_box}
  (h : overlaid_by p₁ p₂) (h₁ : overlaid_by p₂ p₁) : p₁ = p₂ :=
begin
  simp [overlaid_by] at *,
  cases h, cases h₁,
  cases h_left, cases h_right,
  cases h₁_left, cases h₁_right,
  cases p₁, cases p₂,
  congr;
  unfold bounding_box.p₁ bounding_box.p₂ at *;
  cases p₁_p₁; cases p₂_p₂;
  cases p₁_p₂; cases p₂_p₁;
  unfold point.x point.y at *; congr;
  apply le_antisymm; assumption
end

lemma is_in_larger {bb₁ bb₂ : bounding_box} {xy : point}
  (h : is_in_grid bb₁ xy) (h₁ : overlaid_by bb₁ bb₂) : is_in_grid bb₂ xy :=
begin
  unfold overlaid_by is_in_grid is_bounded at *,
  exact and.intro (and.intro (le_trans h₁.right.left h.left.left) 
                             (lt_of_lt_of_le h.left.right h₁.right.right))
                  (and.intro (le_trans h₁.left.left h.right.left)
                             (lt_of_lt_of_le h.right.right h₁.left.right))
end

end finite_grid

section grid_instances

def split_rows_cols : ℕ → ℕ → list string → list string
  | cols 0 ls := [""]
  | cols (k + 1) ls := list.take cols ls ++ ["\n"]
                       ++ split_rows_cols cols k (list.drop cols ls)

def grid_str {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] (g : α) : string :=
  let points := list.map to_string $ decide_grid g in
    " " ++ (list.foldr append "" $
                       list.intersperse " " $
                       split_rows_cols (relative_grid.cols g)
                                       (relative_grid.rows g) points)

instance grid_repr {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] : has_repr α := ⟨grid_str⟩ 

instance grid_to_string {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] : has_to_string α := ⟨grid_str⟩ 

end grid_instances