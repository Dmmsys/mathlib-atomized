/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Kevin H. Wilson
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Bases indexed by `Fin`
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module

open LinearMap

variable {v : ι → M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

namespace Basis

section Fin

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.cons y b`. -/
/-
**Module.Basis.mkFinCons** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mkFinCons {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N) (h
li : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M,
 exists c : R, z + c • y in N) : Basis (Fin (n + 1)) R M
参数：y : M；b : Basis (Fin n) R N；hli : forall (c : R), forall x in N, c • y + x = 
0 -> c = 0；hsp : forall z : M, exists c : R, z + c • y in N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent 
of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.cons y b`.
-/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
/-
**Module.Basis.coe_mkFinCons** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mkFinCons {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N
) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z 
: M, exists c : R, z + c • y in N) : (mkFinCons y b hli hsp : Fin (n + 1) -> M) 
= Fin.cons y ((↑) ∘ b)
参数：y : M；b : Basis (Fin n) R N；hli : forall (c : R), forall x in N, c • y + x = 
0 -> c = 0；hsp : forall z : M, exists c : R, z + c • y in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y ((↑) ∘ b) := by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.cons y b`. -/
/-
**Module.Basis.mkFinConsOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mkFinConsOfLE {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O) (b : B
asis (Fin n) R N) (hNO : N <= O) (hli : forall (c : R), forall x in N, c • y + x
 = 0 -> c = 0) (hsp : forall z in O, exists c : R, z + c • y in N) : Basis (Fin 
(n + 1)) R O
参数：y : M；yO : y in O；b : Basis (Fin n) R N；hNO : N <= O；hli : forall (c : R), fo
rall x in N, c • y + x = 0 -> c = 0；hsp : forall z in O, exists c : R, z + c • y
 in N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of 
`N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.cons y b`.
-/
noncomputable def mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2

@[simp]
/-
**Module.Basis.coe_mkFinConsOfLE** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mkFinConsOfLE {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O) (b
 : Basis (Fin n) R N) (hNO : N <= O) (hli : forall (c : R), forall x in N, c • y
 + x = 0 -> c = 0) (hsp : forall z in O, exists c : R, z + c • y in N) : (mkFinC
onsOfLE y yO b hNO hli hsp : Fin (n + 1) -> O) = Fin.cons ⟨y, yO⟩ (Submodule.inc
lusion hNO ∘ b)
参数：y : M；yO : y in O；b : Basis (Fin n) R N；hNO : N <= O；hli : forall (c : R), fo
rall x in N, c • y + x = 0 -> c = 0；hsp : forall z in O, exists c : R, z + c • y
 in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mkFinCons`：coe_mkFinCons {n : Nat} {N : Submodule R M} 
(y : M) (b : Basis (Fin n) R N) (hli : forall (c : R), forall x in N, c • y + x 
= 0 -> c = 0) (h…
-/
theorem coe_mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) :=
  coe_mkFinCons _ _ _ _

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.snoc b y`. -/
/-
**Module.Basis.mkFinSnoc** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mkFinSnoc {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M) (h
li : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M,
 exists c : R, z + c • y in N) : Basis (Fin (n + 1)) R M
参数：b : Basis (Fin n) R N；y : M；hli : forall (c : R), forall x in N, c • y + x = 
0 -> c = 0；hsp : forall z : M, exists c : R, z + c • y in N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent 
of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.snoc b y`.
-/
noncomputable def mkFinSnoc {n : ℕ} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.snoc (N.subtype ∘ b) y)
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finSnoc' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ ↦ by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
/-
**Module.Basis.coe_mkFinSnoc** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mkFinSnoc {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M
) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z 
: M, exists c : R, z + c • y in N) : (mkFinSnoc b y hli hsp : Fin (n + 1) -> M) 
= Fin.snoc ((↑) ∘ b) y
参数：b : Basis (Fin n) R N；y : M；hli : forall (c : R), forall x in N, c • y + x = 
0 -> c = 0；hsp : forall z : M, exists c : R, z + c • y in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
theorem coe_mkFinSnoc {n : ℕ} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinSnoc b y hli hsp : Fin (n + 1) → M) = Fin.snoc ((↑) ∘ b) y := by
  unfold mkFinSnoc
  exact coe_mk (v := Fin.snoc (N.subtype ∘ b) y) _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.snoc b y`. -/
/-
**Module.Basis.mkFinSnocOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：mkFinSnocOfLE {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N) (hNO
 : N <= O) (y : M) (yO : y in O) (hli : forall (c : R), forall x in N, c • y + x
 = 0 -> c = 0) (hsp : forall z in O, exists c : R, z + c • y in N) : Basis (Fin 
(n + 1)) R O
参数：b : Basis (Fin n) R N；hNO : N <= O；y : M；yO : y in O；hli : forall (c : R), fo
rall x in N, c • y + x = 0 -> c = 0；hsp : forall z in O, exists c : R, z + c • y
 in N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of 
`N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.snoc b y`.
-/
noncomputable def mkFinSnocOfLE {n : ℕ} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (y : M) (yO : y ∈ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinSnoc (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm) ⟨y, yO⟩
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2

@[simp]
/-
**Module.Basis.coe_mkFinSnocOfLE** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_mkFinSnocOfLE {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N) 
(hNO : N <= O) (y : M) (yO : y in O) (hli : forall (c : R), forall x in N, c • y
 + x = 0 -> c = 0) (hsp : forall z in O, exists c : R, z + c • y in N) : (mkFinS
nocOfLE b hNO y yO hli hsp : Fin (n + 1) -> O) = Fin.snoc (Submodule.inclusion h
NO ∘ b) ⟨y, yO⟩
参数：b : Basis (Fin n) R N；hNO : N <= O；y : M；yO : y in O；hli : forall (c : R), fo
rall x in N, c • y + x = 0 -> c = 0；hsp : forall z in O, exists c : R, z + c • y
 in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mkFinSnoc`：coe_mkFinSnoc {n : Nat} {N : Submodule R M} 
(b : Basis (Fin n) R N) (y : M) (hli : forall (c : R), forall x in N, c • y + x 
= 0 -> c = 0) (h…
-/
theorem coe_mkFinSnocOfLE {n : ℕ} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (y : M) (yO : y ∈ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinSnocOfLE b hNO y yO hli hsp : Fin (n + 1) → O) =
      Fin.snoc (Submodule.inclusion hNO ∘ b) ⟨y, yO⟩ :=
  coe_mkFinSnoc _ _ _ _

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
/-
**Module.Basis.finTwoProd** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：(R : Type u_7) → [inst : Semiring R] → Module.Basis (Fin 2) R (R × R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`.
-/
protected def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Module.Basis.finTwoProd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0)
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `finTwoArrowEquiv_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α) = (piFin
TwoEquiv fun x => α).toFun
· 使用定理 `piFinTwoEquiv_apply`：∀ (α : Fin 2 → Type u), ⇑(piFinTwoEquiv α) = fun f 
=> (f 0, f 1)
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `finTwoArrowEquiv_symm_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α).sym
m = fun x => ![x.1, x.2]
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `Module.Basis.ofEquivFun.congr_simp`：∀ {ι : Type u_1} {R : Type u_3} {M :
 Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M] [inst_3 : Finit…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Module.Basis.finTwoProd_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1)
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `finTwoArrowEquiv_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α) = (piFin
TwoEquiv fun x => α).toFun
· 使用定理 `piFinTwoEquiv_apply`：∀ (α : Fin 2 → Type u), ⇑(piFinTwoEquiv α) = fun f 
=> (f 0, f 1)
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `finTwoArrowEquiv_symm_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α).sym
m = fun x => ![x.1, x.2]
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `Module.Basis.ofEquivFun.congr_simp`：∀ {ι : Type u_1} {R : Type u_3} {M :
 Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M] [inst_3 : Finit…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
/-
**Module.Basis.coe_finTwoProd_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) : ⇑((Basis.finTwo
Prod R).repr x) = ![x.fst, x.snd]
参数：x : R × R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl

end Fin

end Basis

end Module

