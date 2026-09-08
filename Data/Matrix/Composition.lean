/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie, Eric Wieser
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Composition of matrices

This file shows that `Mₙ(Mₘ(R)) ≃ Mₙₘ(R)`, `Mₙ(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ`
and also different levels of equivalence when `R` is an `AddCommMonoid`,
`Semiring`, and `Algebra` over a `CommSemiring K`.

## Main definitions

* `Matrix.comp` is an equivalence between `Matrix I J (Matrix K L R)` and
  `I × K` by `J × L` matrices.
* `Matrix.compAddEquiv`: `Matrix.comp` as an `AddEquiv`
* `Matrix.compRingEquiv`: `Matrix.comp` as a `RingEquiv`
* `Matrix.compLinearEquiv`: `Matrix.comp` as a `LinearEquiv`
* `Matrix.compAlgEquiv`: `Matrix.comp` as an `AlgEquiv`
-/

@[expose] public section

namespace Matrix

variable (I J K L R R' : Type*)

/-- An `I` by `J` matrix where each entry is a `K` by `L` matrix is equivalent to
    an `I × K` by `J × L` matrix -/
@[simps]
/-
**Matrix.comp** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where toFun m 
ik jl
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `I` by `J` matrix where each entry is a `K` by `L` matrix is equivalent to
    an `I × K` by `J × L` matrix
-/
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)

section Basic
variable {R I J K L}

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_one [DecidableEq I] [DecidableEq J] [Zero R] [One R] : comp I I J J R
 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
-/
theorem comp_one [DecidableEq I] [DecidableEq J] [Zero R] [One R] : comp I I J J R 1 = 1 := by
  ext; simp only [comp, Equiv.coe_fn_mk, one_apply, apply_ite]; aesop
/-
**Matrix.comp_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_map_map (M : Matrix I J (Matrix K L R)) (f : R -> R') : comp I J K L 
_ (M.map (fun M' => M'.map f)) = (comp I J K L _ M).map f
参数：M : Matrix I J (Matrix K L R)；f : R -> R'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_map_map (M : Matrix I J (Matrix K L R)) (f : R → R') :
    comp I J K L _ (M.map (fun M' => M'.map f)) = (comp I J K L _ M).map f := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**Matrix.comp_single_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_single_single [DecidableEq I] [DecidableEq J] [DecidableEq K] [Decida
bleEq L] [Zero R] (i j k l r) : comp I J K L R (single i j (single k l r)) = sin
gle (i, k) (j, l) r
参数：i j k l r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_of_row_ne`：single_apply_of_row_ne {i i' : m} (hi : i
 != i') (j j' : n) (a : α) : single i j a i' j' = 0
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Matrix.zero_apply`：zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n
 α) i j = 0
· 使用定理 `Matrix.single_apply_of_col_ne`：single_apply_of_col_ne (i i' : m) {j j' :
 n} (hj : j != j') (a : α) : single i j a i' j' = 0
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
-/
theorem comp_single_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) :
    comp I J K L R (single i j (single k l r))
      = single (i, k) (j, l) r := by
  ext ⟨i', k'⟩ ⟨j', l'⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i i'
  · rw [single_apply_of_row_ne hi,
      single_apply_of_row_ne (ne_of_apply_ne Prod.fst hi), Matrix.zero_apply]
  obtain hj | rfl := ne_or_eq j j'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.fst hj), Matrix.zero_apply]
  rw [single_apply_same]
  obtain hk | rfl := ne_or_eq k k'
  · rw [single_apply_of_row_ne hk,
      single_apply_of_row_ne (ne_of_apply_ne Prod.snd hk)]
  obtain hj | rfl := ne_or_eq l l'
  · rw [single_apply_of_col_ne _ _ hj,
      single_apply_of_col_ne _ _ (ne_of_apply_ne Prod.snd hj)]
  rw [single_apply_same, single_apply_same]

@[simp]
/-
**Matrix.comp_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_symm_single [DecidableEq I] [DecidableEq J] [DecidableEq K] [Decidabl
eEq L] [Zero R] (ii jj r) : (comp I J K L R).symm (single ii jj r) = (single ii.
1 jj.1 (single ii.2 jj.2 r))
参数：ii jj r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.comp_single_single`：comp_single_single [DecidableEq I] [Decidable
Eq J] [DecidableEq K] [DecidableEq L] [Zero R] (i j k l r) : comp I J K L R (sin
gle i j (single…
-/
theorem comp_symm_single
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [Zero R] (ii jj r) :
    (comp I J K L R).symm (single ii jj r) =
      (single ii.1 jj.1 (single ii.2 jj.2 r)) :=
  (comp I J K L R).symm_apply_eq.2 <| comp_single_single _ _ _ _ _ |>.symm

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**Matrix.comp_diagonal_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_diagonal_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I -> 
J -> R) : comp I I J J R (diagonal fun i => diagonal fun j => d i j) = diagonal 
fun ij => d ij.1 ij.2
参数：d : I -> J -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Matrix.zero_apply`：zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n
 α) i j = 0
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
theorem comp_diagonal_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I → J → R) :
    comp I I J J R (diagonal fun i => diagonal fun j => d i j)
      = diagonal fun ij => d ij.1 ij.2 := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [comp_apply]
  obtain hi | rfl := ne_or_eq i₁ i₂
  · rw [diagonal_apply_ne _ hi, diagonal_apply_ne _ (ne_of_apply_ne Prod.fst hi),
      Matrix.zero_apply]
  rw [diagonal_apply_eq]
  obtain hj | rfl := ne_or_eq j₁ j₂
  · rw [diagonal_apply_ne _ hj, diagonal_apply_ne _ (ne_of_apply_ne Prod.snd hj)]
  rw [diagonal_apply_eq, diagonal_apply_eq]

@[simp]
/-
**Matrix.comp_symm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_symm_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J -> 
R) : (comp I I J J R).symm (diagonal d) = diagonal fun i => diagonal fun j => d 
(i, j)
参数：d : I × J -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.comp_diagonal_diagonal`：comp_diagonal_diagonal [DecidableEq I] [D
ecidableEq J] [Zero R] (d : I -> J -> R) : comp I I J J R (diagonal fun i => dia
gonal fun j => d i …
-/
theorem comp_symm_diagonal [DecidableEq I] [DecidableEq J] [Zero R] (d : I × J → R) :
    (comp I I J J R).symm (diagonal d) = diagonal fun i => diagonal fun j => d (i, j) :=
  (comp I I J J R).symm_apply_eq.2 <| (comp_diagonal_diagonal fun i j => d (i, j)).symm
/-
**Matrix.comp_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_transpose (M : Matrix I J (Matrix K L R)) : comp J I K L R Mᵀ = (comp
 _ _ _ _ R <| M.map (·ᵀ))ᵀ
参数：M : Matrix I J (Matrix K L R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_transpose (M : Matrix I J (Matrix K L R)) :
    comp J I K L R Mᵀ = (comp _ _ _ _ R <| M.map (·ᵀ))ᵀ := rfl
/-
**Matrix.comp_map_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_map_transpose (M : Matrix I J (Matrix K L R)) : comp I J L K R (M.map
 (·ᵀ)) = (comp _ _ _ _ R Mᵀ)ᵀ
参数：M : Matrix I J (Matrix K L R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_map_transpose (M : Matrix I J (Matrix K L R)) :
    comp I J L K R (M.map (·ᵀ)) = (comp _ _ _ _ R Mᵀ)ᵀ := rfl
/-
**Matrix.comp_symm_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：comp_symm_transpose (M : Matrix (I × K) (J × L) R) : (comp J I L K R).symm
 Mᵀ = (((comp I J K L R).symm M).map (·ᵀ))ᵀ
参数：M : Matrix (I × K) (J × L) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem comp_symm_transpose (M : Matrix (I × K) (J × L) R) :
    (comp J I L K R).symm Mᵀ = (((comp I J K L R).symm M).map (·ᵀ))ᵀ := rfl
/-
**Matrix.transpose_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_comp (M : Matrix I J (Matrix K L R)) : (comp I J K L R M)ᵀ = com
p J I L K R (Mᵀ.map (·ᵀ))
参数：M : Matrix I J (Matrix K L R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_comp (M : Matrix I J (Matrix K L R)) :
    (comp I J K L R M)ᵀ = comp J I L K R (Mᵀ.map (·ᵀ)) :=
  rfl

end Basic

section Add

variable [Add R]

/-- `Matrix.comp` as `AddEquiv` -/
/-
**Matrix.compAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.comp` as `AddEquiv`
-/
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  __ := comp I J K L R
  map_add' _ _ := rfl

@[simp]
/-
**Matrix.compAddEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compAddEquiv_apply (M : Matrix I J (Matrix K L R)) : compAddEquiv I J K L 
R M = comp I J K L R M
参数：M : Matrix I J (Matrix K L R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compAddEquiv_apply (M : Matrix I J (Matrix K L R)) :
    compAddEquiv I J K L R M = comp I J K L R M := rfl

@[simp]
/-
**Matrix.compAddEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compAddEquiv_symm_apply (M : Matrix (I × K) (J × L) R) : (compAddEquiv I J
 K L R).symm M = (comp I J K L R).symm M
参数：M : Matrix (I × K) (J × L) R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compAddEquiv_symm_apply (M : Matrix (I × K) (J × L) R) :
    (compAddEquiv I J K L R).symm M = (comp I J K L R).symm M := rfl

end Add

section AddCommMonoid

variable [AddCommMonoid R] [Mul R] [Fintype I] [Fintype J]

/-- `Matrix.comp` as `RingEquiv` -/
/-
**Matrix.compRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R whe
re __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.comp` as `RingEquiv`
-/
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  __ := compAddEquiv I I J J R
  map_mul' _ _ := by ext; exact sum_apply .. |>.trans <| .symm <| Fintype.sum_prod_type ..

@[simp]
/-
**Matrix.compRingEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compRingEquiv_apply (M : Matrix I I (Matrix J J R)) : compRingEquiv I J R 
M = comp I I J J R M
参数：M : Matrix I I (Matrix J J R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRingEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compRingEquiv I J R M = comp I I J J R M := rfl

@[simp]
/-
**Matrix.compRingEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compRingEquiv_symm_apply (M : Matrix (I × J) (I × J) R) : (compRingEquiv I
 J R).symm M = (comp I I J J R).symm M
参数：M : Matrix (I × J) (I × J) R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRingEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compRingEquiv I J R).symm M = (comp I I J J R).symm M := rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R) [MulOne R] [AddCommMonoid R] [DecidableEq I] [IsStablyFiniteRing R] :
    IsStablyFiniteRing (Matrix I I R) :=
  ⟨fun n ↦ .of_injective (MonoidHom.mk ⟨_, comp_one⟩ (compRingEquiv (Fin n) I R).map_mul)
    (RingEquiv.injective _)⟩

end AddCommMonoid

section LinearMap

variable (R₀ : Type*) [Semiring R₀] [AddCommMonoid R] [Module R₀ R]

/-- `Matrix.comp` as `LinearEquiv` -/
@[simps!]
/-
**Matrix.compLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：compLinearEquiv : Matrix I J (Matrix K L R) ≃ₗ[R₀] Matrix (I × K) (J × L) 
R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.comp` as `LinearEquiv`
-/
def compLinearEquiv : Matrix I J (Matrix K L R) ≃ₗ[R₀] Matrix (I × K) (J × L) R where
  __ := compAddEquiv I J K L R
  map_smul' _ _ := rfl

end LinearMap

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]

variable [DecidableEq I] [DecidableEq J]

/-- `Matrix.comp` as `AlgEquiv` -/
/-
**Matrix.compAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.comp` as `AlgEquiv`
-/
def compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  __ := compRingEquiv I J R
  commutes' _ := comp_diagonal_diagonal _

@[simp]
/-
**Matrix.compAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compAlgEquiv_apply (M : Matrix I I (Matrix J J R)) : compAlgEquiv I J R K 
M = comp I I J J R M
参数：M : Matrix I I (Matrix J J R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compAlgEquiv_apply (M : Matrix I I (Matrix J J R)) :
    compAlgEquiv I J R K M = comp I I J J R M := rfl

@[simp]
/-
**Matrix.compAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：compAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) : (compAlgEquiv I J
 R K).symm M = (comp I I J J R).symm M
参数：M : Matrix (I × J) (I × J) R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compAlgEquiv_symm_apply (M : Matrix (I × J) (I × J) R) :
    (compAlgEquiv I J R K).symm M = (comp I I J J R).symm M := rfl

@[simp]
/-
**Matrix.isUnit_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_comp_iff {M : Matrix I I (Matrix J J R)} : IsUnit (comp _ _ _ _ _ M
) ↔ IsUnit M
参数：Matrix J J R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem isUnit_comp_iff {M : Matrix I I (Matrix J J R)} : IsUnit (comp _ _ _ _ _ M) ↔ IsUnit M :=
  isUnit_map_iff (compAlgEquiv _ _ _ ℕ) M

@[simp]
/-
**Matrix.isUnit_comp_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_comp_symm_iff {M : Matrix (I × J) (I × J) R} : IsUnit (comp _ _ _ _
 _ |>.symm M) ↔ IsUnit M
参数：I × J；I × J。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem isUnit_comp_symm_iff {M : Matrix (I × J) (I × J) R} :
    IsUnit (comp _ _ _ _ _ |>.symm M) ↔ IsUnit M :=
  isUnit_map_iff (compAlgEquiv _ _ _ ℕ).symm M

end Algebra

end Matrix

