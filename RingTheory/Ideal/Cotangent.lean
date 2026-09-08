/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `Ideal.cotangentEquivIdeal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

@[expose] public section


namespace Ideal

-- Universes need to be explicit to avoid bad universe levels in `quotCotangent`
universe u v w

variable {R : Type u} {S : Type v} {S' : Type w} [CommRing R] [CommSemiring S] [Algebra S R]
variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
/-
**Ideal.Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：Cotangent : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I ⧸ I ^ 2` as a quotient of `I`.
-/
def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)
deriving Inhabited

-- The `SMul` instance exists to avoid nsmul and zsmul diamonds.
deriving instance SMul S, AddCommGroup, Module (R ⧸ I), Module S, IsScalarTower S S',
  IsScalarTower R (R ⧸ I) for Cotangent I

variable [IsNoetherian R I] in
deriving instance IsNoetherian R for Cotangent I

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps! -isSimp apply]
/-
**Ideal.toCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：toCotangent : I ->ₗ[R] I.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map from `I` to `I ⧸ I ^ 2`.
-/
def toCotangent : I →ₗ[R] I.Cotangent := Submodule.mkQ _

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.map_toCotangent_ker** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.toCotangent.eq_1`：∀ {R : Type u} [inst : CommRing R] (I : Ideal R)
, I.toCotangent = (I • ⊤).mkQ
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
-/
theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 := by
  rw [Ideal.toCotangent, Submodule.ker_mkQ, pow_two, Submodule.map_smul'' I ⊤ (Submodule.subtype I),
    smul_eq_mul, Submodule.map_subtype_top]
/-
**Ideal.mem_toCotangent_ker** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_toCotangent_ker {x : I} : x in LinearMap.ker I.toCotangent ↔ (x : R) i
n I ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_toCotangent_ker`：map_toCotangent_ker : (LinearMap.ker I.toCota
ngent).map I.subtype = I ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_toCotangent_ker {x : I} : x ∈ LinearMap.ker I.toCotangent ↔ (x : R) ∈ I ^ 2 := by
  rw [← I.map_toCotangent_ker]
  simp
/-
**Ideal.toCotangent_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R)
 in I ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.mem_toCotangent_ker`：mem_toCotangent_ker {x : I} : x in LinearMap.
ker I.toCotangent ↔ (x : R) in I ^ 2
-/
theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 := by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker
/-
**Ideal.toCotangent_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) in I ^ 2
参数：x : I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_toCotangent_ker`：mem_toCotangent_ker {x : I} : x in LinearMap.
ker I.toCotangent ↔ (x : R) in I ^ 2
-/
theorem toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) ∈ I ^ 2 := I.mem_toCotangent_ker
/-
**Ideal.toCotangent_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：toCotangent_surjective : Function.Surjective I.toCotangent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
theorem toCotangent_surjective : Function.Surjective I.toCotangent := Submodule.mkQ_surjective _
/-
**Ideal.toCotangent_range** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：toCotangent_range : LinearMap.range I.toCotangent = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
-/
theorem toCotangent_range : LinearMap.range I.toCotangent = ⊤ := Submodule.range_mkQ _
/-
**Ideal.cotangent_subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.toCotangent_eq_zero`：toCotangent_eq_zero (x : I) : I.toCotangent x
 = 0 ↔ (x : R) in I ^ 2
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.toCotangent_eq`：toCotangent_eq {x y : I} : I.toCotangent x = I.toC
otangent y ↔ (x - y : R) in I ^ 2
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I := by
  constructor
  · intro H
    refine (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) ?_)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
          I.toCotangent_eq.mpr <| ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
/-
**Ideal.cotangentToQuotientSquare** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：cotangentToQuotientSquare : I.Cotangent ->ₗ[R] R ⧸ I ^ 2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`.
-/
def cotangentToQuotientSquare : I.Cotangent →ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype, smul_eq_mul, pow_two])
/-
**Ideal.to_quotient_square_comp_toCotangent** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：to_quotient_square_comp_toCotangent : I.cotangentToQuotientSquare.comp I.t
oCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem to_quotient_square_comp_toCotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl

@[simp]
/-
**Ideal.toCotangent_to_quotient_square** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：toCotangent_to_quotient_square (x : I) : I.cotangentToQuotientSquare (I.to
Cotangent x) = (I ^ 2).mkQ x
参数：x : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCotangent_to_quotient_square (x : I) :
    I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x := rfl
/-
**Ideal.cotangentToQuotientSquare_injective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：cotangentToQuotientSquare_injective : Function.Injective I.cotangentToQuot
ientSquare
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `Ideal.toCotangent_eq_zero`：toCotangent_eq_zero (x : I) : I.toCotangent x
 = 0 ↔ (x : R) in I ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Ideal.toCotangent_to_quotient_square`：toCotangent_to_quotient_square (x 
: I) : I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x
-/
lemma cotangentToQuotientSquare_injective : Function.Injective I.cotangentToQuotientSquare := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rwa [Ideal.toCotangent_eq_zero, ← Submodule.Quotient.mk_eq_zero (I ^ 2)]
/-
**Ideal.Cotangent.smul_eq_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Cotangent
`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {I : Ideal R} {x : R}, x ∈ I → ∀ (m : I
.Cotangent), x • m = 0
参数：m : I.Cotangent。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Ideal.toCotangent_eq_zero`：toCotangent_eq_zero (x : I) : I.toCotangent x
 = 0 ↔ (x : R) in I ^ 2
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}
    {x} (hx : x ∈ I) (m : I.Cotangent) : x • m = 0 := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
  exact Ideal.mul_mem_mul hx m.2
/-
**Ideal.isTorsionBySet_cotangent** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isTorsionBySet_cotangent : Module.IsTorsionBySet R I.Cotangent I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Cotangent.smul_eq_zero_of_mem`：∀ {R : Type u} [inst : CommRing R] 
{I : Ideal R} {x : R}, x ∈ I → ∀ (m : I.Cotangent), x • m = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma isTorsionBySet_cotangent :
    Module.IsTorsionBySet R I.Cotangent I :=
  fun m x ↦ m.smul_eq_zero_of_mem x.2

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
/-
**Ideal.cotangentIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2)
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`.
-/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) :=
  Submodule.map (Quotient.mk (I ^ 2) |>.toSemilinearMap) I
/-
**Ideal.cotangentIdeal_square** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
theorem cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two I.cotangentIdeal, ← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact add_mem hx hy
/-
**Ideal.mk_mem_cotangentIdeal** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：mk_mem_cotangentIdeal {I : Ideal R} {x : R} : Quotient.mk (I ^ 2) x in I.c
otangentIdeal ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
-/
lemma mk_mem_cotangentIdeal {I : Ideal R} {x : R} :
    Quotient.mk (I ^ 2) x ∈ I.cotangentIdeal ↔ x ∈ I := by
  refine ⟨fun ⟨y, hy, e⟩ ↦ ?_, fun h ↦ ⟨x, h, rfl⟩⟩
  simpa using sub_mem hy (Ideal.pow_le_self two_ne_zero
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e))
/-
**Ideal.comap_cotangentIdeal** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_cotangentIdeal (I : Ideal R) : I.cotangentIdeal.comap (Quotient.mk (
I ^ 2)) = I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.mk_mem_cotangentIdeal`：mk_mem_cotangentIdeal {I : Ideal R} {x : R}
 : Quotient.mk (I ^ 2) x in I.cotangentIdeal ↔ x in I
-/
lemma comap_cotangentIdeal (I : Ideal R) :
    I.cotangentIdeal.comap (Quotient.mk (I ^ 2)) = I :=
  Ideal.ext fun _ ↦ mk_mem_cotangentIdeal
/-
**Ideal.range_cotangentToQuotientSquare** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：range_cotangentToQuotientSquare : LinearMap.range I.cotangentToQuotientSqu
are = I.cotangentIdeal.restrictScalars R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Ideal.toCotangent_range`：toCotangent_range : LinearMap.range I.toCotange
nt = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Ideal.to_quotient_square_comp_toCotangent`：to_quotient_square_comp_toCot
angent : I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Subm
odule.subtype I)
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_cotangentToQuotientSquare :
    LinearMap.range I.cotangentToQuotientSquare = I.cotangentIdeal.restrictScalars R := by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
/-
**Ideal.cotangentEquivIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of
 `I` or the
ideal of `R / I ^ 2`.
-/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal := by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by rw [← range_cotangentToQuotientSquare]; exact LinearMap.mem_range_self _ _,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    rw [I.toCotangent_eq]
    dsimp only [toCotangent_to_quotient_square, Submodule.mkQ_apply] at e
    rwa [Submodule.Quotient.eq] at e
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨I.toCotangent ⟨x, hx⟩, Subtype.ext rfl⟩

@[simp]
/-
**Ideal.cotangentEquivIdeal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：cotangentEquivIdeal_apply (x : I.Cotangent) : ↑(I.cotangentEquivIdeal x) =
 I.cotangentToQuotientSquare x
参数：x : I.Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem cotangentEquivIdeal_apply (x : I.Cotangent) :
    ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x := rfl
/-
**Ideal.cotangentEquivIdeal_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：cotangentEquivIdeal_symm_apply (x : R) (hx : x in I) : I.cotangentEquivIde
al.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ = I.toCotangent ⟨x, hx⟩
参数：x : R；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cotangentEquivIdeal_symm_apply (x : R) (hx : x ∈ I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ =
      I.toCotangent ⟨x, hx⟩ := by
  simp [I.cotangentEquivIdeal.symm_apply_eq, Subtype.ext_iff]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

set_option backward.isDefEq.respectTransparency.types false in
/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
/-
**Ideal._root_.AlgHom.kerSquareLift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of 
`f`.
-/
def _root_.AlgHom.kerSquareLift (f : A →ₐ[R] B) : A ⧸ RingHom.ker f.toRingHom ^ 2 →ₐ[R] B := by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r
    rw [IsScalarTower.algebraMap_apply R A, RingHom.toFun_eq_coe, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_mk]
    exact f.map_algebraMap r

-- Can't be `simp`, because `RingHom.ker f.toRingHom` in the definition of `AlgHom.kerSquareLift`
-- is not simp NF. Will be fixed by removing `RingHomClass` in the definition of `RingHom.ker`.
-- (#25138)
/-
**Ideal._root_.AlgHom.kerSquareLift_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgHom.kerSquareLift_mk (f : A →ₐ[R] B) (x : A) : f.kerSquareLift x = f x :=
  rfl
/-
**Ideal._root_.AlgHom.ker_kerSquareLift** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.ker_kerSquareLift (f : A →ₐ[R] B) :
    RingHom.ker f.kerSquareLift.toRingHom = (RingHom.ker f.toRingHom).cotangentIdeal := by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx
/-
**Ideal.Algebra.kerSquareLift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Algebra`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {A : Type u_1} → [inst_1 : Comm
Ring A] → [inst_2 : Algebra R A] → Algebra (R ⧸ RingHom.ker (algebraMap R A) ^ 2
) A
参数：R ⧸ RingHom.ker (algebraMap R A) ^ 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Algebra.kerSquareLift : Algebra (R ⧸ (RingHom.ker (algebraMap R A) ^ 2)) A :=
  (Algebra.ofId R A).kerSquareLift.toAlgebra
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra A B] [IsScalarTower R A B] :
    IsScalarTower R (A ⧸ (RingHom.ker (algebraMap A B) ^ 2)) B :=
  IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R A B).kerSquareLift.comp_algebraMap.symm

/-- The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`. -/
/-
**Ideal.quotCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`.
-/
def quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I := by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `I/I² → J/J²` if `I ≤ f⁻¹(J)`. -/
/-
**Ideal.mapCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：mapCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A ->ₐ[R] B) (h : I₁ <= I₂.
comap f) : I₁.Cotangent ->ₗ[R] I₂.Cotangent
参数：I₁ : Ideal A；I₂ : Ideal B；f : A ->ₐ[R] B；h : I₁ <= I₂.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `I/I² → J/J²` if `I ≤ f⁻¹(J)`.
-/
def mapCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A →ₐ[R] B) (h : I₁ ≤ I₂.comap f) :
    I₁.Cotangent →ₗ[R] I₂.Cotangent := by
  refine Submodule.mapQ ((I₁ • ⊤ : Submodule A I₁).restrictScalars R)
    ((I₂ • ⊤ : Submodule B I₂).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := I₁.restrictScalars R) (q := I₂.restrictScalars R) h
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ (fun _ _ ↦ add_mem)
    rintro a ha ⟨b, hb⟩ -
    simp only [SetLike.mk_smul_mk, smul_eq_mul, Submodule.mem_comap, Submodule.restrictScalars_mem]
    convert!
      (Submodule.smul_mem_smul (M := I₂) (r := f a) (n := ⟨f b, h hb⟩) (h ha)
        (Submodule.mem_top)) using 1
    ext
    exact map_mul f a b

@[simp]
/-
**Ideal.mapCotangent_toCotangent** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：mapCotangent_toCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A ->ₐ[R] B) (h
 : I₁ <= I₂.comap f) (x : I₁) : Ideal.mapCotangent I₁ I₂ f h (Ideal.toCotangent 
I₁ x) = Ideal.toCotangent I₂ ⟨f x, h x.2⟩
参数：I₁ : Ideal A；I₂ : Ideal B；f : A ->ₐ[R] B；h : I₁ <= I₂.comap f；x : I₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma mapCotangent_toCotangent
    (I₁ : Ideal A) (I₂ : Ideal B) (f : A →ₐ[R] B) (h : I₁ ≤ I₂.comap f) (x : I₁) :
    Ideal.mapCotangent I₁ I₂ f h (Ideal.toCotangent I₁ x) = Ideal.toCotangent I₂ ⟨f x, h x.2⟩ := rfl

namespace Cotangent

section Lift

variable {S : Type*} [CommRing S] [Algebra R S] {I : Ideal S}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Lift a linear map `f : I →ₗ[R] M` that vanishes on products to a linear map on the
cotangent space `I ⧸ I ^ 2`. -/
/-
**Ideal.Cotangent.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Cotangent`。
形式化陈述：lift (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) : I.Cotangent
 ->ₗ[R] M where __
参数：f : I ->ₗ[R] M；hf : forall (x y : I), f (x * y) = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a linear map `f : I →ₗ[R] M` that vanishes on products to a linear map on t
he
cotangent space `I ⧸ I ^ 2`.
-/
def lift (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    I.Cotangent →ₗ[R] M where
  __ := QuotientAddGroup.lift _ f.toAddMonoidHom <| fun x hx ↦ by
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    refine Submodule.smul_induction_on hx (fun r hr y _ ↦ hf ⟨r, hr⟩ y) fun x y hx hy ↦ ?_
    simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    exact map_smul f _ _

@[simp]
/-
**Ideal.Cotangent.lift_toCotangent** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotangent`。
形式化陈述：lift_toCotangent (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) (
x : I) : Cotangent.lift f hf (I.toCotangent x) = f x
参数：f : I ->ₗ[R] M；hf : forall (x y : I), f (x * y) = 0；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
-/
lemma lift_toCotangent (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) (x : I) :
    Cotangent.lift f hf (I.toCotangent x) = f x :=
  rfl

@[simp]
/-
**Ideal.Cotangent.lift_comp_toCotangent** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotange
nt`。
形式化陈述：lift_comp_toCotangent (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) =
 0) : Cotangent.lift f hf ∘ₗ I.toCotangent = f
参数：f : I ->ₗ[R] M；hf : forall (x y : I), f (x * y) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.instIsScalarTowerCotangent`：∀ {R : Type u_3} {S : Type u_1} {S' : 
Type u_2} [inst : CommRing R] [inst_1 : CommSemiring S] [inst_2 : Algebra S R]  
 [inst_3 : CommSemirin…
-/
lemma lift_comp_toCotangent (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    Cotangent.lift f hf ∘ₗ I.toCotangent = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.Cotangent.lift_surjective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotangent
`。
形式化陈述：lift_surjective_iff (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0
) : Function.Surjective (Cotangent.lift f hf) ↔ Function.Surjective f
参数：f : I ->ₗ[R] M；hf : forall (x y : I), f (x * y) = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.instIsScalarTowerCotangent`：∀ {R : Type u_3} {S : Type u_1} {S' : 
Type u_2} [inst : CommRing R] [inst_1 : CommSemiring S] [inst_2 : Algebra S R]  
 [inst_3 : CommSemirin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.Cotangent.lift_comp_toCotangent`：lift_comp_toCotangent (f : I ->ₗ[
R] M) (hf : forall (x y : I), f (x * y) = 0) : Cotangent.lift f hf ∘ₗ I.toCotang
ent = f
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `QuotientAddGroup.lift_surjective_of_surjective`：∀ {G : Type u_1} {M : Ty
pe u_4} [inst : AddGroup G] [inst_1 : AddMonoid M] (N : AddSubgroup G) [nN : N.N
ormal]   (φ : G →+ M), Function.Surj…
-/
lemma lift_surjective_iff (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    Function.Surjective (Cotangent.lift f hf) ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Cotangent.lift_comp_toCotangent f hf, LinearMap.coe_comp]
    exact Function.Surjective.comp h (toCotangent_surjective I)
  · dsimp [Cotangent.lift]
    exact QuotientAddGroup.lift_surjective_of_surjective _ _ h _

end Lift

/-- A linear isomorphism between cotangent spaces induced by an equality of ideals. -/
/-
**Ideal.Cotangent.equivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Cotangent`。
形式化陈述：equivOfEq (I J : Ideal R) (hIJ : I = J) : I.Cotangent ≃ₗ[R] J.Cotangent wh
ere __
参数：I J : Ideal R；hIJ : I = J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isomorphism between cotangent spaces induced by an equality of ideals.
-/
def equivOfEq (I J : Ideal R) (hIJ : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent where
  __ := Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) <| fun x y ↦ by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
  invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) <| fun x y ↦ by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    subst hIJ
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp
  right_inv x := by
    subst hIJ
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp

@[simp]
/-
**Ideal.Cotangent.equivOfEq_toCotangent** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotange
nt`。
形式化陈述：equivOfEq_toCotangent (I J : Ideal R) (hIJ : I = J) (x : I) : Cotangent.eq
uivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x)
参数：I J : Ideal R；hIJ : I = J；x : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivOfEq_toCotangent (I J : Ideal R) (hIJ : I = J) (x : I) :
    Cotangent.equivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x) :=
  rfl

@[simp]
/-
**Ideal.Cotangent.equivOfEq_symm** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotangent`。
形式化陈述：equivOfEq_symm (I J : Ideal R) (hIJ : I = J) : (Cotangent.equivOfEq I J hI
J).symm = Cotangent.equivOfEq J I hIJ.symm
参数：I J : Ideal R；hIJ : I = J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivOfEq_symm (I J : Ideal R) (hIJ : I = J) :
    (Cotangent.equivOfEq I J hIJ).symm = Cotangent.equivOfEq J I hIJ.symm :=
  rfl

end Ideal.Cotangent

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
/-
**IsLocalRing.CotangentSpace** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → [IsLocalRing R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `A ⧸ I`-vector space `I ⧸ I ^ 2`.
-/
abbrev CotangentSpace : Type _ := (maximalIdeal R).Cotangent
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (ResidueField R) (CotangentSpace R) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) _
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
  inferInstanceAs <| IsScalarTower R (R ⧸ maximalIdeal R) _

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrictScalars_finite R _ _

variable {R}
/-
**IsLocalRing.subsingleton_cotangentSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
Ring`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R],   Subsingleton (IsLocalRing.CotangentSpace R) ↔ IsField R
参数：IsLocalRing.CotangentSpace R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.cotangent_subsingleton_iff`：cotangent_subsingleton_iff : Subsingle
ton I.Cotangent ↔ IsIdempotentElem I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing`：Ideal.isIdempot
entElem_iff_eq_bot_or_top_of_isLocalRing {R} [CommRing R] [IsNoetherianRing R] [
IsLocalRing R] (I : Ideal R) : IsIdempotentEl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subsingleton_cotangentSpace_iff [IsNoetherianRing R] :
    Subsingleton (CotangentSpace R) ↔ IsField R := by
  refine (maximalIdeal R).cotangent_subsingleton_iff.trans ?_
  rw [IsLocalRing.isField_iff_maximalIdeal_eq,
    Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing]
  simp [(maximalIdeal.isMaximal R).ne_top]
/-
**IsLocalRing.CotangentSpace.map_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRi
ng.CotangentSpace`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R]   {M : Submodule R ↥(IsLocalRing.maximalIdeal R)}, Submodule.map (IsLoc
alRing.maximalIdeal R).toCotangent M = ⊤ ↔ M = ⊤
参数：IsLocalRing.maximalIdeal R；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ideal.map_toCotangent_ker`：map_toCotangent_ker : (LinearMap.ker I.toCota
ngent).map I.subtype = I ^ 2
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.toCotangent_range`：toCotangent_range : LinearMap.range I.toCotange
nt = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CotangentSpace.map_eq_top_iff [IsNoetherianRing R] {M : Submodule R (maximalIdeal R)} :
    M.map (maximalIdeal R).toCotangent = ⊤ ↔ M = ⊤ := by
  refine ⟨fun H ↦ eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp ?_
  rw [Submodule.map_top, Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
  rw [smul_eq_mul, ← pow_two, ← Ideal.map_toCotangent_ker, ← Submodule.map_sup,
    ← Submodule.comap_map_eq, H, Submodule.comap_top, Submodule.map_top, Submodule.range_subtype]
/-
**IsLocalRing.CotangentSpace.span_image_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Is
LocalRing.CotangentSpace`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R]   {s : Set ↥(IsLocalRing.maximalIdeal R)},   Submodule.span (IsLocalRin
g.ResidueField R) (⇑(IsLocalRing.maximalIdeal R).toCotangent '' s) = ⊤ ↔     Sub
module.span R s = ⊤
参数：IsLocalRing.maximalIdeal R；IsLocalRing.ResidueField R；⇑(IsLocalRing.maximalId
eal R).toCotangent '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.CotangentSpace.map_eq_top_iff`：∀ {R : Type u_1} [inst : Comm
Ring R] [inst_1 : IsLocalRing R] [IsNoetherianRing R]   {M : Submodule R ↥(IsLoc
alRing.maximalIdeal R)}, Submod…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueFieldCotangentSpace`：∀ (R : Type u_1
) [inst : CommRing R] [inst_1 : IsLocalRing R],   IsScalarTower R (IsLocalRing.R
esidueField R) (IsLocalRing.CotangentSpace R)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CotangentSpace.span_image_eq_top_iff [IsNoetherianRing R] {s : Set (maximalIdeal R)} :
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s) = ⊤ ↔
      Submodule.span R s = ⊤ := by
  rw [← map_eq_top_iff, ← (Submodule.restrictScalars_injective R ..).eq_iff,
    Submodule.restrictScalars_span]
  · simp
  · exact Ideal.Quotient.mk_surjective

/--
In a local ring with its maximal ideal finitely generated,
the dimension of the cotangent space is equal to the span rank of the maximal ideal.
-/
/-
**IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg** 是 Mathlib 中的一
个定理，位于命名空间 `IsLocalRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R],   (IsLocalR
ing.maximalIdeal R).FG →     Module.rank (IsLocalRing.ResidueField R) (IsLocalRi
ng.CotangentSpace R) =       Submodule.spanRank (IsLocalRing.maximalIdeal R)
参数：IsLocalRing.maximalIdeal R；IsLocalRing.ResidueField R；IsLocalRing.CotangentSp
ace R；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.rank_eq_spanRank_of_free`：Submodule.rank_eq_spanRank_of_free [
Module.Free R M] [StrongRankCondition R] : Module.rank R M = (⊤ : Submodule R M)
.spanRank
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.spanRank_top`：spanRank_top (p : Submodule R M) : (⊤ : Submodul
e R p).spanRank = p.spanRank
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `IsLocalRing.instIsScalarTowerResidueFieldCotangentSpace`：∀ (R : Type u_1
) [inst : CommRing R] [inst_1 : IsLocalRing R],   IsScalarTower R (IsLocalRing.R
esidueField R) (IsLocalRing.CotangentSpace R)
· 使用定理 `Submodule.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff {p : Su
bmodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Ideal.toCotangent_range`：toCotangent_range : LinearMap.range I.toCotange
nt = ⊤
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
· 使用定理 `Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobs
on_bot`：exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot {I 
: Ideal R} {N : Submodule R M} (s : Set (M ⧸ (I • N))) (hN : N.FG) (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
In a local ring with its maximal ideal finitely generated,
the dimension of the cotangent space is equal to the span rank of the maximal id
eal.
-/
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (fg : (maximalIdeal R).FG) :
    Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank := by
  rw [Submodule.rank_eq_spanRank_of_free, ← Submodule.spanRank_top (maximalIdeal R)]
  apply le_antisymm
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule R (maximalIdeal R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s) = ⊤ := by
      rw [← Submodule.restrictScalars_eq_top_iff R,
        Submodule.restrictScalars_span R (ResidueField R) Ideal.Quotient.mk_surjective,
        ← Submodule.map_span, hs_span, Submodule.map_top, Ideal.toCotangent_range]
    rw [← hs_card, ← hs_span']
    grw [Submodule.spanRank_span_le_card, Cardinal.mk_image_le]
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule (ResidueField R) (CotangentSpace R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span R s =
        Submodule.map (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R (maximalIdeal R)))) ⊤ := by
      rw [Submodule.map_top, Submodule.range_mkQ]
      change Submodule.span R s = ⊤
      rw [← Submodule.restrictScalars_span R (ResidueField R)
        Ideal.Quotient.mk_surjective, hs_span, Submodule.restrictScalars_top]
    obtain ⟨t, ht_inj, ht_image, ht_span⟩ :=
      Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot s
        ((Submodule.fg_top (maximalIdeal R)).mpr fg)
        (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
        hs_span'
    rw [← hs_card, ← ht_span, ← ht_image]
    exact le_of_le_of_eq (Submodule.spanRank_span_le_card t)
      (Cardinal.mk_image_eq_of_injOn _ _ ht_inj).symm

/--
In a Noetherian local ring,
the dimension of the cotangent space is equal to the span rank of the maximal ideal.
-/
/-
**IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal** 是 Mathlib 中的一个定理，位于
命名空间 `IsLocalRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R],   Module.rank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace
 R) =     Submodule.spanRank (IsLocalRing.maximalIdeal R)
参数：IsLocalRing.ResidueField R；IsLocalRing.CotangentSpace R；IsLocalRing.maximalId
eal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg`：∀ {R : T
ype u_1} [inst : CommRing R] [inst_1 : IsLocalRing R],   (IsLocalRing.maximalIde
al R).FG →     Module.rank (IsLocalRing.ResidueField…
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG

--- 原说明 ---
In a Noetherian local ring,
the dimension of the cotangent space is equal to the span rank of the maximal id
eal.
-/
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal [IsNoetherianRing R] :
    Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank :=
  rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (maximalIdeal R).fg_of_isNoetherianRing

open Module
/-
**IsLocalRing.finrank_cotangentSpace_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R],   Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSp
ace R) = 0 ↔ IsField R
参数：IsLocalRing.ResidueField R；IsLocalRing.CotangentSpace R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetheria
nRing`：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheri
anRing R],   FiniteDimensional (IsLocalRing.ResidueField R) (IsLoca…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.subsingleton_cotangentSpace_iff`：∀ {R : Type u_1} [inst : Co
mmRing R] [inst_1 : IsLocalRing R] [IsNoetherianRing R],   Subsingleton (IsLocal
Ring.CotangentSpace R) ↔ IsField …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma finrank_cotangentSpace_eq_zero_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 ↔ IsField R := by
  rw [finrank_zero_iff, subsingleton_cotangentSpace_iff]
/-
**IsLocalRing.finrank_cotangentSpace_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalR
ing`。
形式化陈述：∀ (R : Type u_2) [inst : Field R], Module.finrank (IsLocalRing.ResidueFiel
d R) (IsLocalRing.CotangentSpace R) = 0
参数：R : Type u_2；IsLocalRing.ResidueField R；IsLocalRing.CotangentSpace R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.finrank_cotangentSpace_eq_zero_iff`：∀ {R : Type u_1} [inst :
 CommRing R] [inst_1 : IsLocalRing R] [IsNoetherianRing R],   Module.finrank (Is
LocalRing.ResidueField R) (IsLocalRi…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
-/
lemma finrank_cotangentSpace_eq_zero (R) [Field R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 :=
  finrank_cotangentSpace_eq_zero_iff.mpr (Field.toIsField R)

open Submodule in
/-
**IsLocalRing.finrank_cotangentSpace_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheria
nRing R],   Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSp
ace R) ≤ 1 ↔     Submodule.IsPrincipal (IsLocalRing.maximalIdeal R)
参数：IsLocalRing.ResidueField R；IsLocalRing.CotangentSpace R；IsLocalRing.maximalId
eal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_le_one_iff_top_isPrincipal`：Module.finrank_le_one_iff_top
_isPrincipal [Module.Free K V] [Module.Finite K V] : finrank K V <= 1 ↔ (⊤ : Sub
module K V).IsPrincipal
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetheria
nRing`：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetheri
anRing R],   FiniteDimensional (IsLocalRing.ResidueField R) (IsLoca…
· 使用定理 `Submodule.isPrincipal_iff`：∀ {R : Type u_1} {M : Type u_4} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (S : Submodule 
R M), S.IsPrinc…
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem finrank_cotangentSpace_le_one_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) ≤ 1 ↔ (maximalIdeal R).IsPrincipal := by
  rw [Module.finrank_le_one_iff_top_isPrincipal, isPrincipal_iff,
    (maximalIdeal R).toCotangent_surjective.exists, isPrincipal_iff]
  simp_rw [← Set.image_singleton, eq_comm (a := ⊤), CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (injective_subtype _)).eq_iff, map_span, Set.image_singleton,
    Submodule.map_top, range_subtype, eq_comm (a := maximalIdeal R)]
  exact ⟨fun ⟨x, h⟩ ↦ ⟨_, h⟩, fun ⟨x, h⟩ ↦ ⟨⟨x, h ▸ subset_span (Set.mem_singleton x)⟩, h⟩⟩

end IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-
**Ideal.mapCotangent_surjective_of_comap_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cot
angent`。
形式化陈述：Ideal.mapCotangent_surjective_of_comap_eq (surj : Function.Surjective (alg
ebraMap A B)) {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingH
om.ker (algebraMap A B) ⊔ J) : Function.Surjective (Ideal.mapCotangent J I (Alge
bra.ofId A B) (le_of_le_of_eq le_sup_right eq.symm))
参数：surj : Function.Surjective (algebraMap A B)；eq : I.comap (algebraMap A B) = R
ingHom.ker (algebraMap A B) ⊔ J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用引理 `Ideal.exists_of_comap_eq_ker_sup`：Ideal.exists_of_comap_eq_ker_sup {A B 
: Type*} [Ring A] [Ring B] (f : A ->+* B) (surj : Function.Surjective f) {I : Id
eal B} {J : Ideal A} (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearMap.congr_arg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
-/
lemma Ideal.mapCotangent_surjective_of_comap_eq (surj : Function.Surjective (algebraMap A B))
    {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J) :
    Function.Surjective (Ideal.mapCotangent J I (Algebra.ofId A B)
      (le_of_le_of_eq le_sup_right eq.symm)) := by
  intro x
  rcases I.toCotangent_surjective x with ⟨x', rfl⟩
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq x'.2 with ⟨y', mem, hy'⟩
  use J.toCotangent ⟨y', mem⟩
  simpa using I.toCotangent.congr_arg (SetCoe.ext hy')

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.mapCotangent_ker_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Cotangen
t`。
形式化陈述：Ideal.mapCotangent_ker_of_surjective (surj : Function.Surjective (algebraM
ap A B)) {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingHom.ke
r (algebraMap A B) ⊔ J) : (Ideal.mapCotangent J I (Algebra.ofId A B) (le_of_le_o
f_eq le_sup_right eq.symm)).ker = (Submodule.comap J.subtype ((RingHom.ker (alge
braMap A B)) ⊓ J)).map J.toCotangent
参数：surj : Function.Surjective (algebraMap A B)；eq : I.comap (algebraMap A B) = R
ingHom.ker (algebraMap A B) ⊔ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.eq_map_of_comap_eq_ker_sup`：Ideal.eq_map_of_comap_eq_ker_sup {A B 
: Type*} [CommRing A] [CommRing B] (f : A ->+* B) (surj : Function.Surjective f)
 {I : Ideal B} {J : Id…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.add_mem_iff_right`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a
 b : α}, a ∈ I → (a + b ∈ I ↔ b ∈ I)
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `Ideal.toCotangent_eq`：toCotangent_eq {x y : I} : I.toCotangent x = I.toC
otangent y ↔ (x - y : R) in I ^ 2
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `Ideal.mem_inf`：mem_inf {I J : Ideal R} {x : R} : x in I ⊓ J ↔ x in I ∧ x
 in J
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 34 条，此处仅展示前 30 条）
-/
lemma Ideal.mapCotangent_ker_of_surjective (surj : Function.Surjective (algebraMap A B))
    {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J) :
    (Ideal.mapCotangent J I (Algebra.ofId A B) (le_of_le_of_eq le_sup_right eq.symm)).ker =
      (Submodule.comap J.subtype ((RingHom.ker (algebraMap A B)) ⊓ J)).map J.toCotangent := by
  have eqmap := Ideal.eq_map_of_comap_eq_ker_sup _ surj eq
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
    have : Function.Surjective (Algebra.ofId A B) := surj
    simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
      Ideal.toCotangent_eq_zero, eqmap, Algebra.ofId_apply] at hx
    rw [← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ surj] at hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    have : y + z ∈ J := by simp [hyz]
    have zmemJ := (Ideal.add_mem_iff_right J (Ideal.pow_le_self (by omega) hy)).mp this
    have xeq : x = J.toCotangent ⟨z, zmemJ⟩ := by simpa [← hx', J.toCotangent_eq, ← hyz] using hy
    rw [xeq]
    exact Submodule.mem_map_of_mem (Submodule.mem_comap.mpr (Ideal.mem_inf.mpr ⟨hz, zmemJ⟩))
  · rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp]
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Ideal.mapCotangent_toCotangent]
    convert! map_zero I.toCotangent
    exact (Ideal.mem_inf.mp hx).1
