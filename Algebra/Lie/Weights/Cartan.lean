/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Basic

/-!
# Weights and roots of Lie modules and Lie algebras with respect to Cartan subalgebras

Given a Lie algebra `L` which is not necessarily nilpotent, it may be useful to study its
representations by restricting them to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the
particular case when we view `L` as a module over itself via the adjoint action, the weight spaces
of `L` restricted to a nilpotent subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieAlgebra.rootSpace`
  * `LieAlgebra.corootSpace`
  * `LieAlgebra.rootSpaceWeightSpaceProduct`
  * `LieAlgebra.rootSpaceProduct`
  * `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`

-/

@[expose] public section

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

open scoped TensorProduct
open TensorProduct.LieModule LieModule

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
/-
**LieAlgebra.rootSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpace (χ : H -> R) : LieSubmodule R H L
参数：χ : H -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is
 the weight
space of `L` regarded as a module of `H` via the adjoint action.
-/
abbrev rootSpace (χ : H → R) : LieSubmodule R H L :=
  genWeightSpace L χ
/-
**LieAlgebra.zero_rootSpace_eq_top_of_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra`。
形式化陈述：zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] : rootSpace (⊤ 
: LieSubalgebra R L) 0 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.zero_genWeightSpace_eq_top_of_nilpotent`：zero_genWeightSpace_e
q_top_of_nilpotent [IsNilpotent L M] : genWeightSpace M (0 : (⊤ : LieSubalgebra 
R L) -> R) = ⊤
-/
theorem zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_genWeightSpace_eq_top_of_nilpotent L

@[simp]
/-
**LieAlgebra.rootSpace_comap_eq_genWeightSpace** 是 Mathlib 中的一个定理，位于命名空间 `LieAlg
ebra`。
形式化陈述：rootSpace_comap_eq_genWeightSpace (χ : H -> R) : (rootSpace H χ).comap H.i
ncl' = genWeightSpace H χ
参数：χ : H -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.comap_genWeightSpace_eq_of_injective`：comap_genWeightSpace_eq_
of_injective (hf : Injective f) : (genWeightSpace M₂ χ).comap f = genWeightSpace
 M χ
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem rootSpace_comap_eq_genWeightSpace (χ : H → R) :
    (rootSpace H χ).comap H.incl' = genWeightSpace H χ :=
  comap_genWeightSpace_eq_of_injective Subtype.coe_injective

variable {H}
/-
**LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace** 是 Mathlib 中的一个定理，位于命
名空间 `LieAlgebra`。
形式化陈述：lie_mem_genWeightSpace_of_mem_genWeightSpace {χ₁ χ₂ : H -> R} {x : L} {m :
 M} (hx : x in rootSpace H χ₁) (hm : m in genWeightSpace M χ₂) : ⁅x, m⁆ in genWe
ightSpace M (χ₁ + χ₂)
参数：hx : x in rootSpace H χ₁；hm : m in genWeightSpace M χ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.genWeightSpace.eq_1`：∀ {R : Type u_2} {L : Type u_3} (M : Type
 u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst
_3 : AddCommGroup M…
· 使用定理 `LieSubmodule.mem_iInf`：mem_iInf {ι} (p : ι -> LieSubmodule R L M) {x} : 
x in ⨅ i, p i ↔ forall i, x in p i
· 使用定理 `LieAlgebra.rootSpace.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : CommR
ing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) 
[inst_3 : LieRi…
· 使用引理 `LieModule.lie_mem_maxGenEigenspace_toEnd`：lie_mem_maxGenEigenspace_toEnd
 {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y in 𝕎(L, χ₁, x)) (hm : m in 𝕎(M, χ₂, x)) :
 ⁅y, m⁆ in 𝕎(M, χ₁ + χ₂, x)
-/
theorem lie_mem_genWeightSpace_of_mem_genWeightSpace {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) :
    ⁅x, m⁆ ∈ genWeightSpace M (χ₁ + χ₂) := by
  rw [genWeightSpace, LieSubmodule.mem_iInf]
  intro y
  replace hx : x ∈ genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace, genWeightSpace, LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m ∈ genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace, LieSubmodule.mem_iInf] at hm; exact hm y
  exact lie_mem_maxGenEigenspace_toEnd hx hm
/-
**LieAlgebra.toEnd_pow_apply_mem** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：toEnd_pow_apply_mem {χ₁ χ₂ : H -> R} {x : L} {m : M} (hx : x in rootSpace 
H χ₁) (hm : m in genWeightSpace M χ₂) (n) : (toEnd R L M x ^ n : Module.End R M)
 m in genWeightSpace M (n • χ₁ + χ₂)
参数：hx : x in rootSpace H χ₁；hm : m in genWeightSpace M χ₂；n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace`：lie_mem_genWeig
htSpace_of_mem_genWeightSpace {χ₁ χ₂ : H -> R} {x : L} {m : M} (hx : x in rootSp
ace H χ₁) (hm : m in genWeightSpace M χ₂) : ⁅…
-/
lemma toEnd_pow_apply_mem {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) (n) :
    (toEnd R L M x ^ n : Module.End R M) m ∈ genWeightSpace M (n • χ₁ + χ₂) := by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul, ← add_assoc, add_comm (n • _)]
/-
**LieAlgebra.mem_biSup_genWeightSpace_of** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：mem_biSup_genWeightSpace_of {s : Set (H -> R)} (hs : forallᵉ (χ₁ in s) (χ₂
 in s), χ₁ + χ₂ in s) {x : L} {m : M} (hx : x in ⨆ χ, ⨆ (_ : χ in s), rootSpace 
H χ) (hm : m in ⨆ χ, ⨆ (_ : χ in s), genWeightSpace M χ) : ⁅x, m⁆ in ⨆ χ, ⨆ (_ :
 χ in s), genWeightSpace M χ
参数：H -> R；hs : forallᵉ (χ₁ in s) (χ₂ in s), χ₁ + χ₂ in s；hx : x in ⨆ χ, ⨆ (_ : χ
 in s), rootSpace H χ；hm : m in ⨆ χ, ⨆ (_ : χ in s), genWeightSpace M χ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.iSup_induction'`：iSup_induction' {ι} (N : ι -> LieSubmodule
 R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx 
: x in N i), motiv…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι} {b : M} {N : ι -> LieS
ubmodule R L M} (i : ι) (h : b in N i) : b in ⨆ i, N i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
-/
lemma mem_biSup_genWeightSpace_of {s : Set (H → R)} (hs : ∀ᵉ (χ₁ ∈ s) (χ₂ ∈ s), χ₁ + χ₂ ∈ s)
    {x : L} {m : M} (hx : x ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ)
    (hm : m ∈ ⨆ χ, ⨆ (_ : χ ∈ s), genWeightSpace M χ) :
    ⁅x, m⁆ ∈ ⨆ χ, ⨆ (_ : χ ∈ s), genWeightSpace M χ := by
  induction hx using LieSubmodule.iSup_induction' with
  | zero => simp
  | add _ _ _ _ hu hv => rw [add_lie]; exact add_mem hu hv
  | mem χ₁ u hu =>
    by_cases hχ₁ : χ₁ ∈ s; swap
    · simp_all
    replace hu : u ∈ rootSpace H χ₁ := by simpa [hχ₁] using hu
    induction hm using LieSubmodule.iSup_induction' with
    | zero => simp
    | add _ _ _ _ hv hw => rw [lie_add]; exact add_mem hv hw
    | mem χ₂ v hv =>
      by_cases hχ₂ : χ₂ ∈ s; swap
      · simp_all
      apply LieSubmodule.mem_iSup_of_mem (χ₁ + χ₂)
      simp_all [lie_mem_genWeightSpace_of_mem_genWeightSpace]

variable (R L H M)

/-- Auxiliary definition for `rootSpaceWeightSpaceProduct`,
which is close to the deterministic timeout limit.
-/
/-
**LieAlgebra.rootSpaceWeightSpaceProductAux** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebr
a`。
形式化陈述：rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H -> R} (hχ : χ₁ + χ₂ = χ₃) : r
ootSpace H χ₁ ->ₗ[R] genWeightSpace M χ₂ ->ₗ[R] genWeightSpace M χ₃ where toFun 
x
参数：hχ : χ₁ + χ₂ = χ₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `rootSpaceWeightSpaceProduct`,
which is close to the deterministic timeout limit.
-/
def rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H → R} (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ →ₗ[R] genWeightSpace M χ₂ →ₗ[R] genWeightSpace M χ₃ where
  toFun x :=
    { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆,
          hχ ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add, AddMemClass.mk_add_mk]
      map_smul' := fun t m => by simp }
  map_add' x y := by
    ext m
    simp only [LieSubmodule.coe_add, add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      AddMemClass.mk_add_mk]
  map_smul' t x := by
    simp only [RingHom.id_apply]
    ext m
    simp only [SetLike.val_smul, smul_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      SetLike.mk_smul_mk]

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the actions of `H`. -/
/-
**LieAlgebra.rootSpaceWeightSpaceProduct** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) : root
Space H χ₁ otimes[R] genWeightSpace M χ₂ ->ₗ⁅R,H⁆ genWeightSpace M χ₃
参数：χ₁ χ₂ χ₃ : H -> R；hχ : χ₁ + χ₂ = χ₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is
 a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the act
ions of `H`.
-/
def rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] genWeightSpace M χ₂ →ₗ⁅R,H⁆ genWeightSpace M χ₃ :=
  liftLie R H (rootSpace H χ₁) (genWeightSpace M χ₂) (genWeightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux]
        dsimp
        simp only [lie_lie] }

@[simp]
/-
**LieAlgebra.coe_rootSpaceWeightSpaceProduct_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Algebra`。
形式化陈述：coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ
₃) (x : rootSpace H χ₁) (m : genWeightSpace M χ₂) : (rootSpaceWeightSpaceProduct
 R L H M χ₁ χ₂ χ₃ hχ (x otimesₜ m) : M) = ⁅(x : L), (m : M)⁆
参数：χ₁ χ₂ χ₃ : H -> R；hχ : χ₁ + χ₂ = χ₃；x : rootSpace H χ₁；m : genWeightSpace M χ
₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.LieModule.coe_liftLie_eq_lift_coe`：coe_liftLie_eq_lift_coe
 (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) : ⇑(liftLie R L M N P f) = lift R L M N P f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : genWeightSpace M χ₂) :
    (rootSpaceWeightSpaceProduct R L H M χ₁ χ₂ χ₃ hχ (x ⊗ₜ m) : M) = ⁅(x : L), (m : M)⁆ := by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    lift_apply, LinearMap.coe_mk, AddHom.coe_mk]
/-
**LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace** 是 Mathlib 中的一个定理
，位于命名空间 `LieAlgebra`。
形式化陈述：mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace (α χ : H -> R) {x : L} (h
x : x in rootSpace H α) : MapsTo (toEnd R L M x) (genWeightSpace M χ) (genWeight
Space M (α + χ))
参数：α χ : H -> R；hx : x in rootSpace H α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace (α χ : H → R)
    {x : L} (hx : x ∈ rootSpace H α) :
    MapsTo (toEnd R L M x) (genWeightSpace M χ) (genWeightSpace M (α + χ)) := by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' ⊗ₜ m')).property

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`. -/
/-
**LieAlgebra.rootSpaceProduct** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpaceProduct (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) : rootSpace H χ₁ 
otimes[R] rootSpace H χ₂ ->ₗ⁅R,H⁆ rootSpace H χ₃
参数：χ₁ χ₂ χ₃ : H -> R；hχ : χ₁ + χ₂ = χ₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is
 a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`.
-/
def rootSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] rootSpace H χ₂ →ₗ⁅R,H⁆ rootSpace H χ₃ :=
  rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ

@[simp]
/-
**LieAlgebra.rootSpaceProduct_def** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduc
t R L H L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L := rfl
/-
**LieAlgebra.rootSpaceProduct_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpaceProduct_tmul (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpa
ce H χ₁) (y : rootSpace H χ₂) : (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x otimesₜ y
) : L) = ⁅(x : L), (y : L)⁆
参数：χ₁ χ₂ χ₃ : H -> R；hχ : χ₁ + χ₂ = χ₃；x : rootSpace H χ₁；y : rootSpace H χ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.coe_rootSpaceWeightSpaceProduct_tmul`：coe_rootSpaceWeightSpac
eProduct_tmul (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (m : 
genWeightSpace M χ₂) : (rootSpaceWeig…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rootSpaceProduct_tmul
    (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (y : rootSpace H χ₂) :
    (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x ⊗ₜ y) : L) = ⁅(x : L), (y : L)⁆ := by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H → R` is a Lie
subalgebra of `L`. -/
/-
**LieAlgebra.zeroRootSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：zeroRootSubalgebra : LieSubalgebra R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H 
→ R` is a Lie
subalgebra of `L`.
-/
def zeroRootSubalgebra : LieSubalgebra R L :=
  { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 ⊗[R] rootSpace H 0 := ⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) ∈ rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe_mk, Subtype.coe_mk] at this
      exact (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy).property }

@[simp]
/-
**LieAlgebra.coe_zeroRootSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = root
Space H 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl
/-
**LieAlgebra.mem_zeroRootSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：mem_zeroRootSubalgebra (x : L) : x in zeroRootSubalgebra R L H ↔ forall y 
: H, exists k : Nat, (toEnd R H L y ^ k) x = 0
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_zeroRootSubalgebra (x : L) :
    x ∈ zeroRootSubalgebra R L H ↔ ∀ y : H, ∃ k : ℕ, (toEnd R H L y ^ k) x = 0 := by
  change x ∈ rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]
/-
**LieAlgebra.toLieSubmodule_le_rootSpace_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra`。
形式化陈述：toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule <= rootSpace H 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
· 使用定理 `LieModule.iterate_toEnd_mem_lowerCentralSeries`：iterate_toEnd_mem_lowerC
entralSeries (x : L) (m : M) (k : Nat) : (toEnd R L M x)^[k] m in lowerCentralSe
ries R L M k
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
-/
theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule ≤ rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [Module.End.commute_pow_left_of_commute hfg k]
  have h := iterate_toEnd_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk, LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, Module.End.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h

/-- This enables the instance `Zero (Weight R H L)`. -/
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This enables the instance `Zero (Weight R H L)`.
-/
instance [Nontrivial H] : Nontrivial (genWeightSpace L (0 : H → R)) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩
/-
**LieAlgebra.le_zeroRootSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：le_zeroRootSubalgebra : H <= zeroRootSubalgebra R L H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (
K : Submodule R L) <= K' ↔ K <= K'
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
· 使用定理 `LieAlgebra.coe_zeroRootSubalgebra`：coe_zeroRootSubalgebra : (zeroRootSub
algebra R L H : Submodule R L) = rootSpace H 0
· 使用定理 `LieSubmodule.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (N
 : Submodule R M) <= N' ↔ N <= N'
· 使用定理 `LieAlgebra.toLieSubmodule_le_rootSpace_zero`：toLieSubmodule_le_rootSpace
_zero : H.toLieSubmodule <= rootSpace H 0
-/
theorem le_zeroRootSubalgebra : H ≤ zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, ← H.coe_toLieSubmodule,
    coe_zeroRootSubalgebra, LieSubmodule.toSubmodule_le_toSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H

@[simp]
/-
**LieAlgebra.zeroRootSubalgebra_normalizer_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Li
eAlgebra`。
形式化陈述：zeroRootSubalgebra_normalizer_eq_self : (zeroRootSubalgebra R L H).normali
zer = zeroRootSubalgebra R L H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.mem_zeroRootSubalgebra`：mem_zeroRootSubalgebra (x : L) : x in
 zeroRootSubalgebra R L H ↔ forall y : H, exists k : Nat, (toEnd R H L y ^ k) x 
= 0
· 使用定理 `LieSubalgebra.mem_normalizer_iff`：mem_normalizer_iff (x : L) : x in H.no
rmalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H
· 使用定理 `LieAlgebra.le_zeroRootSubalgebra`：le_zeroRootSubalgebra : H <= zeroRootS
ubalgebra R L H
· 使用定理 `Module.End.iterate_succ`：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (
f' ^ n) f'
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `Submodule.coe_mk`：coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `LieSubalgebra.le_normalizer`：le_normalizer : H <= H.normalizer
-/
theorem zeroRootSubalgebra_normalizer_eq_self :
    (zeroRootSubalgebra R L H).normalizer = zeroRootSubalgebra R L H := by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew, map_neg, neg_eq_zero] at hk
  use k + 1
  rw [Module.End.iterate_succ, LinearMap.coe_comp, Function.comp_apply, toEnd_apply_apply,
    LieSubalgebra.coe_bracket_of_module, Submodule.coe_mk, hk]

/-- If the zero root subalgebra of a nilpotent Lie subalgebra `H` is just `H` then `H` is a Cartan
subalgebra.

When `L` is Noetherian, it follows from Engel's theorem that the converse holds. See
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan` -/
/-
**LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra`。
形式化陈述：is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) : H.
IsCartanSubalgebra
参数：h : zeroRootSubalgebra R L H = H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.zeroRootSubalgebra_normalizer_eq_self`：zeroRootSubalgebra_nor
malizer_eq_self : (zeroRootSubalgebra R L H).normalizer = zeroRootSubalgebra R L
 H

--- 原说明 ---
If the zero root subalgebra of a nilpotent Lie subalgebra `H` is just `H` then `
H` is a Cartan
subalgebra.

When `L` is Noetherian, it follows from Engel's theorem that the converse holds.
 See
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`
-/
theorem is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra :=
  { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }

@[simp]
/-
**LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra`。
形式化陈述：zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSuba
lgebra] [IsNoetherian R L] : zeroRootSubalgebra R L H = H
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.isNilpotent_iff_exists_self_le_ucs`：isNilpotent_iff_exists_
self_le_ucs : LieModule.IsNilpotent L N ↔ exists k, N <= (⊥ : LieSubmodule R L M
).ucs k
· 使用定理 `LieModule.instIsNilpotentSubtypeMemLieSubmoduleGenWeightSpaceOfNatForall
OfIsNoetherian`：∀ {R : Type u_2} {L : Type u_3} (M : Type u_4) [inst : CommRing 
R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LieSubmodule.ucs_le_of_normalizer_eq_self`：ucs_le_of_normalizer_eq_self 
(h : N₁.normalizer = N₁) (k : Nat) : (⊥ : LieSubmodule R L M).ucs k <= N₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.normalizer_eq_self_of_isCartanSubalgebra`：normalizer_eq_se
lf_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] : H.toLi
eSubmodule.normalizer = H.toLieSubmodule
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieAlgebra.le_zeroRootSubalgebra`：le_zeroRootSubalgebra : H <= zeroRootS
ubalgebra R L H
-/
theorem zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [IsNoetherian R L] : zeroRootSubalgebra R L H = H := by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 ≤ H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)
/-
**LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan** 是 Mathlib 中的一个定理，位于命名空间 `LieA
lgebra`。
形式化陈述：zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] : zeroRootSubalgebr
a R L H = H ↔ H.IsCartanSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq`：is_cartan_of_zeroRootSuba
lgebra_eq (h : zeroRootSubalgebra R L H = H) : H.IsCartanSubalgebra
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan`：zeroRootSubalgebra_eq_of_
is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] : ze
roRootSubalgebra R L H = H
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra :=
  ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩
/-
**LieAlgebra.eq_rootSpace_zero_iff_isCartan** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebr
a`。
形式化陈述：eq_rootSpace_zero_iff_isCartan [IsNoetherian R L] : H.toLieSubmodule = roo
tSpace H 0 ↔ H.IsCartanSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`：zeroRootSubalgebra_eq_if
f_is_cartan [IsNoetherian R L] : zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalg
ebra
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_rootSpace_zero_iff_isCartan [IsNoetherian R L] :
    H.toLieSubmodule = rootSpace H 0 ↔ H.IsCartanSubalgebra := by
  rw [← zeroRootSubalgebra_eq_iff_is_cartan, ← LieSubalgebra.toSubmodule_inj,
    ← LieSubmodule.toSubmodule_inj]
  aesop

@[simp]
/-
**LieAlgebra.rootSpace_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoethe
rian R L] : rootSpace H 0 = H.toLieSubmodule
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieAlgebra.coe_zeroRootSubalgebra`：coe_zeroRootSubalgebra : (zeroRootSub
algebra R L H : Submodule R L) = rootSpace H 0
· 使用定理 `LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan`：zeroRootSubalgebra_eq_of_
is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] : ze
roRootSubalgebra R L H = H
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
-/
theorem rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] :
    rootSpace H 0 = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj, ← coe_zeroRootSubalgebra,
    zeroRootSubalgebra_eq_of_is_cartan R L H, LieSubalgebra.coe_toLieSubmodule]

variable {R L H}
variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

/-- Given a root `α` relative to a Cartan subalgebra `H`, this is the span of all products of
an element of the `α` root space and an element of the `-α` root space. Informally it is often
denoted `⁅H(α), H(-α)⁆`.

If the Killing form is non-degenerate and the coefficients are a perfect field, this space is
one-dimensional. See `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton` and
`LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton'`.

Note that the name "coroot space" is not standard as this space does not seem to have a name in the
informal literature. -/
/-
**LieAlgebra.corootSpace** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：corootSpace : LieIdeal R H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a root `α` relative to a Cartan subalgebra `H`, this is the span of all pr
oducts of
an element of the `α` root space and an element of the `-α` root space. Informal
ly it is often
denoted `⁅H(α), H(-α)⁆`.

If the Killing form is non-degenerate and the coefficients are a perfect field, 
this space is
one-dimensional. See `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton` an
d
`LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton'`.

Note that the name "coroot space" is not standard as this space does not seem to
 have a name in the
informal literature.
-/
def corootSpace : LieIdeal R H :=
  LieModuleHom.range <| ((rootSpace H 0).incl.comp <|
    rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p ↦ (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) p).property)

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.mem_corootSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：mem_corootSpace {x : H} : x in corootSpace α ↔ (x : L) in Submodule.span R
 {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.corootSpace.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   {H : LieSubalgebra R L
} [inst_3 : LieRi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.map_span`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ 
: Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_corootSpace {x : H} :
    x ∈ corootSpace α ↔
    (x : L) ∈ Submodule.span R {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} := by
  have : x ∈ corootSpace α ↔
      (x : L) ∈ LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simp only [rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw [this, corootSpace, ← LieModuleHom.map_top, ← LieSubmodule.mem_toSubmodule,
    LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule, ← TensorProduct.span_tmul_eq_top,
    LinearMap.map_span, Set.image, Set.mem_ofPred_eq, exists_exists_exists_and_eq]
  change (x : L) ∈ Submodule.span R
    {x | ∃ (a : rootSpace H α) (b : rootSpace H (-α)), ⁅(a : L), (b : L)⁆ = x} ↔ _
  simp
/-
**LieAlgebra.mem_corootSpace'** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：mem_corootSpace' {x : H} : x in corootSpace α ↔ x in Submodule.span R ({⁅y
, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} : Set H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `LieAlgebra.coe_rootSpaceWeightSpaceProduct_tmul`：coe_rootSpaceWeightSpac
eProduct_tmul (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (m : 
genWeightSpace M χ₂) : (rootSpaceWeig…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Submodule.coe_subtype`：coe_subtype : (Submodule.subtype p : p -> M) = Su
btype.val
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用引理 `LieAlgebra.mem_corootSpace`：mem_corootSpace {x : H} : x in corootSpace α
 ↔ (x : L) in Submodule.span R {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H 
(-α))}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_corootSpace' {x : H} :
    x ∈ corootSpace α ↔
    x ∈ Submodule.span R ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H) := by
  set s : Set H := ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [SetLike.mem_coe]
    rw [← Submodule.mem_map, Submodule.coe_subtype, Submodule.map_span, mem_corootSpace, ← this]
  ext u
  simp only [Submodule.coe_subtype, mem_image, Subtype.exists, LieSubalgebra.mem_toSubmodule,
    exists_and_right, exists_eq_right, mem_ofPred_eq, s]
  refine ⟨fun ⟨_, y, hy, z, hz, hyz⟩ ↦ ⟨y, hy, z, hz, hyz⟩,
    fun ⟨y, hy, z, hz, hyz⟩ ↦ ⟨?_, y, hy, z, hz, hyz⟩⟩
  convert!
    (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) (⟨y, hy⟩ ⊗ₜ[R] ⟨z, hz⟩)).property using 0
  simp [hyz]

section FiniteDimensional

variable {K : Type*} [Field K] [LieAlgebra K L]
variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [LieModule.IsTriangularizable K H L]

/-
**LieAlgebra.lieIdeal_eq_iSup_inf_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra`。
形式化陈述：lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) : I.restr H = ⨆ χ :
 Weight K H L, I.restr H ⊓ genWeightSpace L χ
参数：I : LieIdeal K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.eq_iSup_inf_genWeightSpace`：eq_iSup_inf_genWeightSpace [IsTria
ngularizable K L M] (N : LieSubmodule K L M) : N = ⨆ χ : Weight K L M, N ⊓ genWe
ightSpace M χ
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
-/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.restr H = ⨆ χ : Weight K H L, I.restr H ⊓ genWeightSpace L χ :=
  eq_iSup_inf_genWeightSpace (N := I.restr H)
/-
**LieAlgebra.lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace** 是 Mathlib 中的一个引理，位
于命名空间 `LieAlgebra`。
形式化陈述：lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) : I.rest
r H = (I.restr H ⊓ H.toLieSubmodule) ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), 
I.restr H ⊓ rootSpace H α
参数：I : LieIdeal K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.lieIdeal_eq_iSup_inf_genWeightSpace`：lieIdeal_eq_iSup_inf_gen
WeightSpace (I : LieIdeal K L) : I.restr H = ⨆ χ : Weight K H L, I.restr H ⊓ gen
WeightSpace L χ
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), I.restr H ⊓ rootSpace H α := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ ↦ inf_le_left))
  conv_lhs => rw [lieIdeal_eq_iSup_inf_genWeightSpace]
  exact iSup_le fun α ↦ by
    by_cases hα : α.IsZero
    · rw [show genWeightSpace L (α : H → K) = H.toLieSubmodule by ext; simp [hα.eq]]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
/-
**LieAlgebra.cartan_sup_iSup_rootSpace_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra`。
形式化陈述：cartan_sup_iSup_rootSpace_eq_top : H.toLieSubmodule ⊔ ⨆ α : Weight K H L, 
⨆ (_ : α.IsNonZero), rootSpace H α = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top'`：iSup_genWeightSpace_eq_top' [IsTr
iangularizable K L M] : ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  rw [eq_top_iff, ← LieModule.iSup_genWeightSpace_eq_top', iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
  · exact le_sup_of_le_right <| le_iSup₂_of_le α hα (le_refl _)

end FiniteDimensional

end LieAlgebra

