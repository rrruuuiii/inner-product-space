-- since F is not specified to be R or C, the dealing with type castings make some proofs below
-- rather tedious.

import data.complex.is_R_or_C
import data.real.sqrt
import data.real.basic

open_locale complex_conjugate


structure inner_product_space (V : Type*) (F : Type*) 
  -- method to define module at https://leanprover-community.github.io/theories/linear_algebra.html
  -- the module enables the scalor multiplication between elements of Type F and elements of Type V
  [add_comm_group V] [is_R_or_C F] [module F V] := 
  (inner_product : V → V → F)
  (conjugate_symmetry : ∀ x y, inner_product x y = conj (inner_product y x))
  (linear_prod_left : ∀ (x y: V) (a: F), inner_product (a • x) y = a * inner_product x y)
  (linear_add_left: ∀ (x y z: V), inner_product (x + y) z = inner_product x z + inner_product y z)
  -- note that conjugate symmetry implies that the inner product is a real number (imaganary part is 
  -- 0):
  (im_zero: ∀ x y: V, is_R_or_C.im (inner_product x y) = 0)
  -- we are using the positive semi-definite Hermitian form here:
  (nonnegative : ∀ x, is_R_or_C.re (inner_product x x) ≥ 0)
  (positive_semi_definite : ∀ x, is_R_or_C.re (inner_product x x) = 0 → x = 0)
  -- we define the norm here:
  (norm' : V → ℝ)
  (norm_eq_sqrt_inner_prod : ∀ x, norm' x = real.sqrt (is_R_or_C.re (inner_product x x)))

namespace inner_product_space 

variables {V F : Type*} [add_comm_group V] [is_R_or_C F] [module F V] 
variables inner_prod_space : inner_product_space V F

local notation `⟆`x, y`⟆` := inner_prod_space.inner_product x y

theorem inner_prod_is_real (x y: V) : (is_R_or_C.re ⟆x, y⟆ : F) = ⟆x, y⟆ :=
begin
  rw is_R_or_C.ext_iff, split,
  { rw is_R_or_C.of_real_re },
  { rw is_R_or_C.of_real_im,
    rw inner_prod_space.im_zero }
end

theorem commutative (x y: V) : ⟆x, y⟆ = ⟆y, x⟆ :=
begin
  rw conjugate_symmetry,
  rw <-inner_prod_is_real,
  rw is_R_or_C.conj_of_real,
end

theorem zero_mul (x: V) : ⟆0, x⟆ = 0 := 
begin
  rw <-zero_smul F x,
  rw inner_prod_space.linear_prod_left,
  rw zero_mul,
end

theorem real_nonneg (x: V) : is_R_or_C.re ⟆x, x⟆ ≥ 0 :=
by apply inner_prod_space.nonnegative


theorem inner_prod_zero_iff_self_zero (x: V) : ⟆x, x⟆ = 0 ↔ x = 0 :=
begin
  rw <-inner_prod_is_real, split,
  { simp,
    exact inner_prod_space.positive_semi_definite x },
  { intro h, rw h,
    rw zero_mul, simp }
end

theorem linear_left (x y z: V) (a b: F) : ⟆a • x + b • y, z⟆ = a * ⟆x, z⟆ + b * ⟆y, z⟆ :=
begin
  rw inner_prod_space.linear_add_left (a • x) (b • y) z,
  simp [inner_prod_space.linear_prod_left],
end

theorem linear_right (x y z: V) (a b: F) : ⟆x, a • y + b • z⟆ = a * ⟆x, y⟆ + b * ⟆x, z⟆ :=
begin 
  rw commutative,
  rw inner_prod_space.linear_add_left (a • y) (b • z) x,
  simp [inner_prod_space.linear_prod_left],
  simp [commutative],
end

theorem linear_prod_right (x y: V) (a: F) : ⟆x, a • y⟆ = a * ⟆x, y⟆ :=
begin
  rw [commutative, linear_prod_left],
  simp [commutative],
end

theorem linear_add_right (x y z: V) : ⟆x, y + z⟆ = ⟆x, y⟆ + ⟆x, z⟆ :=
begin
  rw [commutative, linear_add_left],
  simp [commutative],
end

theorem inner_prod_of_add_add (x y z: V) : 
  ⟆x + y, x + y⟆ = ⟆x, x⟆ + 2 * ⟆x, y⟆ + ⟆y, y⟆ :=
begin
  rw linear_add_right,
  simp [linear_add_left],
  simp [commutative], ring,
end

open is_R_or_C real
local notation `‖`x`‖` := inner_prod_space.norm' x

theorem norm_nonneg' (x: V) : 0 ≤ ‖x‖ :=
begin
  rw norm_eq_sqrt_inner_prod,
  apply sqrt_nonneg,
end

theorem norm_up_eq_norm (x: V) : (re ‖x‖ : F) = ‖x‖ :=
by exact rfl

theorem norm_im_eq_zero (x: V) : im ‖x‖ = 0 :=
begin
  rw is_R_or_C.ext_iff, split,
  { simp }, { simp },
end

theorem re_of_norm_eq_norm (x: V) : re ‖x‖ = ‖x‖ :=
begin
  rw is_R_or_C.ext_iff, split,
  { simp }, { simp },
end

theorem re_of_norm_squared_eq_norm_squared (x: V) : re (‖x‖^2) = ‖x‖^2 :=
begin
  rw is_R_or_C.ext_iff, split,
  { simp }, { simp },
end

theorem norm_squared_eq_re_inner_prod (x: V) : ‖x‖^2 = re (⟆x, x⟆) :=
begin
  rw [norm_eq_sqrt_inner_prod, sq_sqrt],
  apply nonnegative,
end

theorem norm_squared_eq_inner_prod (x: V) : (‖x‖^2 : F) = ⟆x, x⟆ :=
begin
  rw [<-inner_prod_is_real, <-norm_squared_eq_re_inner_prod],
  simp,
end

theorem norm_squared_eq_inner_prod' (x: V) : ‖x‖^2 = re (⟆x, x⟆) :=
begin
  rw [norm_eq_sqrt_inner_prod, sq_sqrt],
  apply nonnegative,
end

theorem sum_of_F_eq_re_of_sum_of_F (A B : V) : 
  (‖A‖ : F) + (‖B‖ : F) = re ((‖A‖ : F) + (‖B‖ : F)) :=
by simp

theorem norm_squared  (A B : V) : 
  (‖A‖ + ‖B‖) ^ 2 = (‖A‖ ^ 2) + (‖B‖ ^ 2) + 2 * (‖A‖ * ‖B‖) :=
by ring

theorem re_sum_squared_eq_re_of_sum_squared (A B : V) : 
  re ((‖A‖ : F) + (‖B‖ : F)) ^ 2 = re (((‖A‖ : F) + (‖B‖ : F)) ^ 2) :=
begin
  ring_nf,
  simp [norm_squared_eq_inner_prod],
  rw norm_squared,
  rw [<-norm_squared_eq_re_inner_prod], ring,
end

theorem re_of_sum_of_norm_nonneg (A B : V): 
  re ((‖A‖ : F) + (‖B‖ : F)) >= 0 :=
begin
  simp, apply add_nonneg,
  { exact inner_prod_space.norm_nonneg' A },
  { exact inner_prod_space.norm_nonneg' B }, 
end

theorem conj_of_inner_prod_eq_inner_prod (x : V) :
  conj (⟆x, x⟆) = ⟆x, x⟆ :=
begin
  rw is_R_or_C.ext_iff, split,
  { simp },
  { simp, rw im_zero, ring },
end

theorem inner_prod_of_smul (x : V) (a : F) :
  ⟆a • x, a • x⟆ = a * (conj a) * ⟆x, x⟆ :=
begin
  rw inner_prod_space.linear_prod_left x (a • x) a,
  rw conjugate_symmetry,
  rw inner_prod_space.linear_prod_left x x a,
  simp, rw conj_of_inner_prod_eq_inner_prod, ring,
end

theorem re_inner_prod_nonneg (x : V) :
  0 <= re (⟆x, x⟆) :=
begin
  have := inner_prod_space.nonnegative x, 
  linarith,
end

theorem sqrt_of_re_of_norm_squared_eq_norm (x : V):
  sqrt (re ((‖x‖ ^ 2 : ℝ) : F)) = ‖x‖ :=
begin
  simp,
  rw inner_prod_space.norm_squared_eq_inner_prod x,
  rw <-(inner_prod_space.norm_squared_eq_re_inner_prod x),
  exact sqrt_sq (inner_prod_space.norm_nonneg' x),
end

theorem absolute_homogeneity (x : V) (a : F) : 
  ‖a • x‖ = (abs a) * ‖x‖ :=
begin
  have h1 := inner_prod_space.inner_prod_of_smul x a,
  have : a * conj a = ↑(norm_sq a),
  { rw [mul_comm, conj_mul_eq_norm_sq_left a] },
  rw this at h1, clear this,
  rw <-(inner_prod_space.inner_prod_is_real (a • x) (a • x)) at h1,
  rw <-(inner_prod_space.inner_prod_is_real x x) at h1,
  rw <-(inner_prod_space.norm_squared_eq_re_inner_prod (a • x)) at h1,
  rw <-(inner_prod_space.norm_squared_eq_re_inner_prod x) at h1,
  apply_fun (λ x, sqrt (re x)) at h1,
  have : sqrt (re ↑(inner_prod_space.norm' (a • x) ^ 2)) = inner_prod_space.norm' (a • x),
  { exact inner_prod_space.sqrt_of_re_of_norm_squared_eq_norm (a • x) },
  rw this at h1, clear this,
  rw h1, clear h1, simp,
  rw inner_prod_space.norm_squared_eq_inner_prod,
  rw sqrt_mul' (norm_sq a) (inner_prod_space.re_inner_prod_nonneg x),
  rw norm_sq_eq_def',
  rw sqrt_sq (norm_nonneg a),
  rw is_R_or_C.norm_eq_abs a,
  rw norm_eq_sqrt_inner_prod,
end

theorem norm_plus_norm_eq_plus_norm_iff_inner_product_eq_product_norms (A B : V) : 
  ‖A‖ + ‖B‖ = ‖A + B‖ ↔ ⟆A, B⟆ = ‖A‖ * ‖B‖ :=
begin
  split,
  { intro h1, apply_fun (λ x, x ^ 2) at h1,
    rw norm_squared_eq_inner_prod' at h1,
    have h2 : (‖A‖ + ‖B‖)^2 = ‖A‖^2 + 2*‖A‖*‖B‖ + ‖B‖^2,
    { ring },
    rw h2 at h1, clear h2,
    simp [norm_squared_eq_inner_prod'] at h1,
    rw inner_prod_of_add_add at h1,
    simp [inner_prod_is_real] at h1,
    apply_fun (λ x, x / 2) at h1,
    have h3 : 2 * ‖A‖ * ‖B‖ / 2 = ‖A‖ * ‖B‖,
    { ring },
    rw h3 at h1, clear h3,
    have h4 : 2 * re (⟆A, B⟆) / 2 = re (⟆A, B⟆),
    { ring },
    rw h4 at h1, clear h4,
    rw <-inner_prod_is_real,
    rw is_R_or_C.ext_iff, split,
    { simp, rw <-h1 }, { simp }, 
    exact A },
  { intro h1,
    apply_fun (λ x, 2 * x) at h1,
    apply_fun (λ x, x + ⟆A,A⟆ + ⟆B,B⟆) at h1,
    rw [<-norm_squared_eq_inner_prod] at h1,
    rw [<-norm_squared_eq_inner_prod] at h1,
    have h2 : 2 * ((‖A‖ : F) * (‖B‖ : F)) + (‖A‖ : F) ^ 2 + (‖B‖ : F) ^ 2 = ((‖A‖ : F) + (‖B‖ : F)) ^ 2,
    { ring },
    rw h2 at h1, clear h2,
    rw [norm_squared_eq_inner_prod] at h1,
    rw [norm_squared_eq_inner_prod] at h1,
    have h2 : 2 * ⟆A, B⟆ + ⟆A, A⟆ + ⟆B, B⟆ = ⟆A + B, A + B⟆,
    { rw inner_prod_space.inner_prod_of_add_add,
      ring,
      exact A },
    rw h2 at h1, clear h2,
    rw inner_prod_space.norm_eq_sqrt_inner_prod (A+B),
    rw h1, clear h1,
    rw [<-re_sum_squared_eq_re_of_sum_squared],
    have h' : re ((‖A‖ : F) + (‖B‖ : F)) >= 0,
    { exact inner_prod_space.re_of_sum_of_norm_nonneg A B },
    rw sqrt_sq h',
    rw sum_of_F_eq_re_of_sum_of_F, simp },
end

theorem plus_distributivity (A B : V) :
  ⟆A + B, A + B⟆ = ⟆A, A⟆ + 2 * ⟆A, B⟆ + ⟆B,B⟆ :=
begin
  simp [linear_add_left],
  rw [commutative, linear_add_left],
  rw inner_prod_space.commutative B (A + B),
  rw linear_add_left,
  rw inner_prod_space.commutative B _, ring,
end

theorem inner_prod_neg_eq_neg_inner_prod (A B : V):
  ⟆A, -B⟆ = - ⟆A, B⟆ :=
begin
  apply_fun (λ x, x + ⟆A, B⟆), simp,
  have := inner_prod_space.linear_add_right A (-B) B,
  rw <-this, clear this, simp,
  { rw commutative,
    rw zero_mul },
  { exact add_left_injective (inner_prod_space.inner_product A B) },
end

theorem inner_prod_of_neg_eq_inner_prod (A : V):
  ⟆-A, -A⟆ = ⟆A, A⟆ :=
begin
  rw [inner_prod_neg_eq_neg_inner_prod, commutative],
  apply_fun (λ x, x + ⟆A, -A⟆), simp,
  { have := inner_prod_space.linear_add_right A A (-A),
    rw <-this, clear this,
    simp,
    rw [commutative, zero_mul] },
  { exact add_left_injective (inner_prod_space.inner_product A (-A)) },
end

theorem minus_distributivity (A B : V) :
  ⟆A - B, A - B⟆ = ⟆A, A⟆ - 2 * ⟆A, B⟆ + ⟆B,B⟆ :=
begin
  have : A - B = A + (-B),
  { apply_fun (λ x, x + B), simp,
    exact add_left_injective B },
  simp [this], clear this,
  simp [linear_add_left],
  rw [commutative, linear_add_left],
  rw inner_prod_space.commutative (-B) (A + (-B)),
  rw linear_add_left,
  rw inner_prod_space.commutative (-B), ring_nf,
  rw inner_prod_neg_eq_neg_inner_prod,
  rw inner_prod_of_neg_eq_inner_prod, ring,
end

theorem parallelogram_law (A B : V) : 
  ‖A + B‖^2 + ‖A - B‖^2 = 2 * (‖A‖^2 + ‖B‖^2) :=
begin
  simp [norm_squared_eq_re_inner_prod],
  rw [plus_distributivity, minus_distributivity],
  simp, ring,
end

theorem polorazation_identity (A B : V) :
  ‖A + B‖^2 = ‖A‖^2 + ‖B‖^2 + 2 * (re (⟆A, B⟆)) :=
begin 
  rw [norm_squared_eq_re_inner_prod, plus_distributivity], simp,
  simp [<-norm_squared_eq_inner_prod'], ring,
end 

theorem conj_of_norm_squared_eq_norm_squared (A : V) :
  conj ((‖A‖ : F)^2) = ‖A‖^2 := by simp

theorem re_of_conj_of_inner_prod_eq_inner_prod (u v : V) :
  re (conj (⟆u, v⟆)) = re (⟆u, v⟆) := by simp

theorem real_of_norm_squared_eq_F_of_norm_squared (v : V) :
  ((‖v‖ ^ 2 : ℝ) : F) = (‖v‖ : F) ^ 2 := by simp

theorem re_of_re_eq_re (x : F) :
  re (re x) = re x := by simp

theorem squared_of_F_of_norm_eq_F_of_squared_of_norm (v : V):
  (‖v‖ : F) ^ 2 = ((‖v‖ ^ 2 : ℝ) : F) := by simp

theorem F_of_real_mul_F_of_real_eq_F_of_prod (x y : ℝ) :
  ((x * y : ℝ) : F) = ((x : F) * (y : F)) := by simp

theorem squared_of_F_of_real_eq_F_of_squared_of_real (r : ℝ) : 
  ((r : ℝ) : F) ^ 2 = ((r ^ 2 : ℝ) : F) := by simp

theorem up_sub_up_eq_up_dif (r1 r2 : ℝ) : 
  ((r1 : ℝ) : F) - ((r2 : ℝ) : F) = ((r1 - r2 : ℝ) : F) := by simp

theorem re_of_F_of_real_eq_real (r : ℝ) : 
  re ((r : ℝ) : F) = r := by simp 

-- the following proofs follow "proof1" on wekepedia of Cauchy Schwarz Inequality:
theorem helper_equation (u v: V) :
  re (((‖v‖) : F) ^ 2 * (((‖v‖) : F) ^ 2 * ((‖u‖) : F) ^ 2 - ((re (⟆u, v⟆)) : F) ^ 2))
  =
  ‖v‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - re (⟆u, v⟆) ^ 2) :=
begin
  rw ext_iff, split,
  { rw re_of_re_eq_re, 
    rw squared_of_F_of_norm_eq_F_of_squared_of_norm,
    rw squared_of_F_of_norm_eq_F_of_squared_of_norm,
    rw of_real_mul_re,
    rw <-F_of_real_mul_F_of_real_eq_F_of_prod,
    rw squared_of_F_of_real_eq_F_of_squared_of_real,
    rw up_sub_up_eq_up_dif,
    rw re_of_F_of_real_eq_real, simp, left, ring },
  { simp },
end

theorem equation1 (u v : V):
  ‖(‖v‖^2 : F) • u - ⟆u, v⟆ • v‖^2 = ‖v‖^2 * (‖u‖^2 * ‖v‖^2 - (re (⟆u, v⟆))^2) :=
begin
  rw inner_prod_space.norm_squared_eq_inner_prod' (↑(‖v‖) ^ 2 • u - ⟆u, v⟆ • v),
  rw minus_distributivity,
  rw inner_prod_of_smul,
  rw conj_of_norm_squared_eq_norm_squared,
  have : ⟆(↑(‖v‖) ^ 2 • u), (⟆u, v⟆ • v)⟆ = ‖v‖^2 * re (conj (⟆u, v⟆)) *  re (⟆u, v⟆),
  { rw linear_prod_left,
    rw commutative,
    rw linear_prod_left,
    rw inner_prod_space.commutative v u,
    rw re_of_conj_of_inner_prod_eq_inner_prod,
    simp [inner_prod_is_real], ring },
  rw this, clear this,  
  have : ⟆(⟆u, v⟆ • v), (⟆u, v⟆ • v)⟆ = re (⟆u, v⟆) * conj (re (⟆u, v⟆)) * re (⟆v, v⟆),
  { rw linear_prod_left,
    rw inner_prod_space.commutative v,
    rw linear_prod_left,
    simp,
    simp [inner_prod_is_real], ring },
  rw this, clear this,
  rw two_mul,
  rw <-norm_squared_eq_inner_prod',
  rw sub_add,
  have : conj (re (⟆u, v⟆)) = re (conj (⟆u, v⟆)),
  { simp },
  rw this, clear this,
  have : ↑(‖v‖) ^ 2 * ↑(re (conj (⟆u, v⟆))) * ↑(re (⟆u, v⟆)) = ↑(re (⟆u, v⟆)) * ↑(re (conj (⟆u, v⟆))) * ↑(‖v‖ ^ 2),
  { simp, rw mul_comm (↑(‖v‖) ^ 2) (↑(re (⟆u, v⟆))),
    ring },
  rw this, clear this,
  rw [<-add_sub, sub_self, add_zero],
  rw re_of_conj_of_inner_prod_eq_inner_prod,
  rw <-sq (↑(re (⟆u, v⟆))),
  rw mul_comm (↑(re (⟆u, v⟆))^2),
  rw real_of_norm_squared_eq_F_of_norm_squared,
  rw [mul_assoc, <-mul_sub, <-norm_squared_eq_inner_prod],
  exact inner_prod_space.helper_equation u v,
end

theorem norm_of_zero_eq_zero (v : V) : 
  ‖0‖ = 0 :=
begin
  rw [norm_eq_sqrt_inner_prod, zero_mul], simp, 
end

theorem div_mul_div_self (r1 r2 : ℝ) (pre : r1 ≠ 0) : 
  (r1 * r2) / r1 = r2 :=
by rw [mul_comm, mul_div_cancel r2 pre]
 
theorem cauchy_schwarz_inequality' (u v : V) :
  (re (⟆u, v⟆))^2 <= ‖u‖^2 * ‖v‖^2 :=
begin
  by_cases (v = 0),
  { rw h, rw [commutative, zero_mul, norm_of_zero_eq_zero],
    simp, exact u },
  { have h1 := inner_prod_space.equation1 u v,
    apply_fun (λ x, x / (‖v‖ ^ 2)) at h1,
    rw mul_comm,
    have := div_mul_div_self (‖v‖^2) (inner_prod_space.norm' u ^ 2 * inner_prod_space.norm' v ^ 2 - re (inner_prod_space.inner_product u v) ^ 2),
    rw this at h1, clear this,
    { have : inner_prod_space.norm' (↑(inner_prod_space.norm' v) ^ 2 • u - inner_prod_space.inner_product u v • v) ^ 2 / inner_prod_space.norm' v ^ 2 ≥ 0,
      { apply div_nonneg,
        { apply sq_nonneg (inner_prod_space.norm' (↑(inner_prod_space.norm' v) ^ 2 • u - ⟆u, v⟆ • v)) },
        { apply sq_nonneg } },
      { rw h1 at this, clear h1,
        simp at this,
        rw mul_comm at this,
        exact this } },
    { clear this, clear h1,
      rw inner_prod_space.norm_eq_sqrt_inner_prod,
      rw sq_sqrt,
      { intro h',
        have := inner_prod_space.positive_semi_definite v h',
        contradiction },
      { apply nonnegative } } } 
end

theorem mul_of_squares_eq_square_of_mul (r1 r2 : ℝ) :
  r1^2 * r2^2 = (r1 * r2)^2 := by ring

theorem cauchy_schwarz_inequality (u v : V) :
  re (⟆u, v⟆) ≤ ‖u‖ * ‖v‖ :=
begin
  by_cases h1 : (v = 0),
  { rw h1, rw [commutative, zero_mul, norm_of_zero_eq_zero],
    simp, exact u },
  { have h2:= inner_prod_space.cauchy_schwarz_inequality' u v,
    rw mul_of_squares_eq_square_of_mul (‖u‖) (‖v‖) at h2, 
    rw sq_le_sq at h2,
    have : 0 ≤ inner_prod_space.norm' u * inner_prod_space.norm' v,
    { apply mul_nonneg,
      { apply norm_nonneg' },
      { apply norm_nonneg' } },
    rw <-abs_eq_self at this, rw this at h2, clear this,
    have := abs_cases (re (inner_prod_space.inner_product u v)),
    cases this with h3 h4,
    { cases h3 with h5 h6,
      { rw h5 at h2, exact h2 } },
    { cases h4 with h7 h8,
      { linarith } } }
end

theorem triangular_inequality (A B : V) :
  ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
begin
  suffices h1 : ‖A + B‖^2 ≤ (‖A‖ + ‖B‖) ^ 2,
  { have h2 : 0 ≤ (‖A‖ + ‖B‖) ^ 2,
    { apply pow_two_nonneg },
    have h3 := sqrt_le_sqrt_iff h2, clear h2,
    { rw ← h3 at h1, 
      rw sqrt_sq (inner_prod_space.norm_nonneg' (A + B)) at h1,
      have h4 : ‖A‖ + ‖B‖ ≥ 0,
      { apply add_nonneg,
        { apply norm_nonneg' },
        { apply norm_nonneg' } },
      rw real.sqrt_sq h4 at h1, clear h4,
      exact h1 } },
  suffices h1 : re (⟆A, B⟆) ≤ ‖A‖ * ‖B‖,
  { have h2 : re (⟆A, A⟆) + 2 * re (⟆A, B⟆) + re (⟆B, B⟆) ≤  ‖A‖ ^ 2 + 2 * ‖A‖ * ‖B‖ + ‖B‖ ^ 2,
    { apply add_le_add,
      { apply add_le_add,
        { rw norm_squared_eq_re_inner_prod },
        { linarith } },
      { rw norm_squared_eq_re_inner_prod } },
    have h3 : (‖A‖ + ‖B‖) ^ 2 = ‖A‖ ^ 2 + 2 * ‖A‖ * ‖B‖ + ‖B‖ ^ 2,
    { linarith },
    rw h3, clear h3, rw polorazation_identity,
    have h4 : ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * re (⟆A, B⟆) = re (⟆A, A⟆) + 2 * re (⟆A, B⟆) + re (⟆B, B⟆),
    { simp [norm_squared_eq_re_inner_prod], ring },
    rw h4, clear h4, exact h2 },
  { exact inner_prod_space.cauchy_schwarz_inequality A B },
end


end inner_product_space