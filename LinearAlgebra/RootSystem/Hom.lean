/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Basic
public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Morphisms of root pairings

This file defines morphisms of root pairings, following the definition of morphisms of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
* `Hom`: A morphism of root pairings is a linear map of weight spaces, its transverse on coweight
  spaces, and a bijection on the set that indexes roots and coroots.
* `Hom.id`: The identity morphism.
* `Hom.comp`: The composite of two morphisms.
* `End`: The endomorphism monoid of a root pairing.
* `Hom.weightHom`: The homomorphism from the endomorphism monoid to linear endomorphisms on the
  weight space.
* `Hom.coweightHom`: The homomorphism from the endomorphism monoid to the opposite monoid of linear
  endomorphisms on the coweight space.
* `Equiv`: An equivalence of root pairings is a morphism for which the maps on weight spaces and
  coweight spaces are bijective.
* `Equiv.toHom`: The morphism underlying an equivalence.
* `Equiv.weightEquiv`: The linear isomorphism on weight spaces given by an equivalence.
* `Equiv.coweightEquiv`: The linear isomorphism on coweight spaces given by an equivalence.
* `Equiv.id`: The identity equivalence.
* `Equiv.comp`: The composite of two equivalences.
* `Equiv.symm`: The inverse of an equivalence.
* `Aut`: The automorphism group of a root pairing.
* `Equiv.toEndUnit`: The group isomorphism between the automorphism group of a root pairing and the
  group of invertible endomorphisms.
* `Equiv.weightHom`: The homomorphism from the automorphism group to linear automorphisms on the
  weight space.
* `Equiv.coweightHom`: The homomorphism from the automorphism group to the opposite group of linear
  automorphisms on the coweight space.
* `Equiv.reflection`: The automorphism of a root pairing given by reflection in a root and
  coreflection in the corresponding coroot.

## TODO
* Special types of morphisms: Isogenies, weight/coweight space embeddings
* Weyl group reimplementation?

-/

@[expose] public section

open Set Function

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A morphism of root pairings is a pair of mutually transposed maps of weight and coweight spaces
that preserves roots and coroots.  We make the map of indexing sets explicit. -/
@[ext]
/-
**RootPairing.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   {ι₂ : Type u_5} 
→                     {M₂ : Type u_6} →                       {N₂ : Type u_7} → 
                        [inst_5 : AddCommGroup M₂] →                           [
inst_6 : _root_.Module R M₂] →                             [inst_7 : AddCommGrou
p N₂] →                               [inst_8 : _root_.Module R N₂] →           
                      RootPairing ι R M N →                                   Ro
otPairing ι₂ R M₂ N₂ → Type (max (max (max (max (max u_1 u_3) u_4) u_5) u_6) u_7
)
参数：max (max (max (max (max u_1 u_3) u_4) u_5) u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of root pairings is a pair of mutually transposed maps of weight and 
coweight spaces
that preserves roots and coroots.  We make the map of indexing sets explicit.
-/
structure Hom {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) where
  /-- A linear map on weight space. -/
  weightMap : M →ₗ[R] M₂
  /-- A contravariant linear map on coweight space. -/
  coweightMap : N₂ →ₗ[R] N
  /-- A bijection on index sets. -/
  indexEquiv : ι ≃ ι₂
  weight_coweight_transpose :
    weightMap.dualMap ∘ₗ Q.flip.toPerfPair = P.flip.toPerfPair ∘ₗ coweightMap
  root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
  coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm

namespace Hom

/-
**RootPairing.Hom.weight_coweight_transpose_apply** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing.Hom`。
形式化陈述：weight_coweight_transpose_apply {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Modu
le R M₂] [AddCommGroup N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPair
ing ι₂ R M₂ N₂) (x : N₂) (f : Hom P Q) : f.weightMap.dualMap (Q.flip.toPerfPair 
x) = P.flip.toPerfPair (f.coweightMap x)
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；x : N₂；f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `RootPairing.Hom.weight_coweight_transpose`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]  
 [inst_2 : _root_.Module R M] […
-/
lemma weight_coweight_transpose_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (x : N₂) (f : Hom P Q) :
    f.weightMap.dualMap (Q.flip.toPerfPair x) = P.flip.toPerfPair (f.coweightMap x) :=
  Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x
/-
**RootPairing.Hom.root_weightMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ho
m`。
形式化陈述：root_weightMap_apply {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [A
ddCommGroup N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂
 N₂) (i : ι) (f : Hom P Q) : f.weightMap (P.root i) = Q.root (f.indexEquiv i)
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；i : ι；f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `RootPairing.Hom.root_weightMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma root_weightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι) (f : Hom P Q) :
    f.weightMap (P.root i) = Q.root (f.indexEquiv i) :=
  Eq.mp (propext funext_iff) f.root_weightMap i
/-
**RootPairing.Hom.coroot_coweightMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Hom`。
形式化陈述：coroot_coweightMap_apply {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂
] [AddCommGroup N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ 
R M₂ N₂) (i : ι₂) (f : Hom P Q) : f.coweightMap (Q.coroot i) = P.coroot (f.index
Equiv.symm i)
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；i : ι₂；f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `RootPairing.Hom.coroot_coweightMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
-/
lemma coroot_coweightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι₂) (f : Hom P Q) :
    f.coweightMap (Q.coroot i) = P.coroot (f.indexEquiv.symm i) :=
  Eq.mp (propext funext_iff) f.coroot_coweightMap i

/-- The identity morphism of a root pairing. -/
@[simps!]
/-
**RootPairing.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Hom`。
形式化陈述：id (P : RootPairing ι R M N) : Hom P P where weightMap
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity morphism of a root pairing.
-/
def id (P : RootPairing ι R M N) : Hom P P where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp

/-- Composition of morphisms -/
@[simps!]
/-
**RootPairing.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Hom`。
形式化陈述：comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommG
roup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module
 R N₂] {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing
 ι₂ R M₂ N₂} (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where weightMap
参数：g : Hom P₁ P₂；f : Hom P P₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of morphisms
-/
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap, ← LinearMap.comp_assoc _ f.coweightMap,
      ← f.weight_coweight_transpose, LinearMap.comp_assoc g.coweightMap,
      ← g.weight_coweight_transpose, ← LinearMap.comp_assoc]
  root_weightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.coe_trans]
    rw [comp_assoc, f.root_weightMap, ← comp_assoc, g.root_weightMap, comp_assoc]
  coroot_coweightMap := by
    ext i
    simp only [LinearMap.coe_comp]
    rw [comp_assoc, g.coroot_coweightMap, ← comp_assoc, f.coroot_coweightMap, comp_assoc]
    simp

@[simp]
/-
**RootPairing.Hom.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：id_comp {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N
₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom
 P Q) : comp f (id P) = f
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Hom.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Modu
le R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
-/
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp f (id P) = f := by
  ext x <;> simp

@[simp]
/-
**RootPairing.Hom.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：comp_id {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N
₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom
 P Q) : comp (id Q) f = f
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Hom.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Modu
le R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Hom.id_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
-/
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp (id Q) f = f := by
  ext x <;> simp

@[simp]
/-
**RootPairing.Hom.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module 
R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGr
oup N₂] [Module R N₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module 
R N₃] {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing 
ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃} (h : Hom P₂ P₃) (g : Hom P₁ P₂) (f : H
om P P₁) : comp (comp h g) f = comp h (comp g f)
参数：h : Hom P₂ P₃；g : Hom P₁ P₂；f : Hom P P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Hom.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Modu
le R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
-/
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : Hom P₂ P₃) (g : Hom P₁ P₂) (f : Hom P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp

/-- The endomorphism monoid of a root pairing. -/
/-
**RootPairing.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism monoid of a root pairing.
-/
instance (P : RootPairing ι R M N) : Monoid (Hom P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P

@[simp]
/-
**RootPairing.Hom.weightMap_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：weightMap_one (P : RootPairing ι R M N) : weightMap (P
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightMap_one (P : RootPairing ι R M N) :
    weightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl

@[simp]
/-
**RootPairing.Hom.coweightMap_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：coweightMap_one (P : RootPairing ι R M N) : coweightMap (P
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightMap_one (P : RootPairing ι R M N) :
    coweightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl

@[simp]
/-
**RootPairing.Hom.indexEquiv_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：indexEquiv_one (P : RootPairing ι R M N) : indexEquiv (P
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma indexEquiv_one (P : RootPairing ι R M N) :
    indexEquiv (P := P) (Q := P) 1 = Equiv.refl ι :=
  rfl

@[simp]
/-
**RootPairing.Hom.weightMap_mul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：weightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) : weightMap (x * y
) = weightMap x ∘ₗ weightMap y
参数：P : RootPairing ι R M N；x y : Hom P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    weightMap (x * y) = weightMap x ∘ₗ weightMap y :=
  rfl

@[simp]
/-
**RootPairing.Hom.coweightMap_mul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：coweightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) : coweightMap (x
 * y) = coweightMap y ∘ₗ coweightMap x
参数：P : RootPairing ι R M N；x y : Hom P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    coweightMap (x * y) = coweightMap y ∘ₗ coweightMap x :=
  rfl

@[simp]
/-
**RootPairing.Hom.indexEquiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom`。
形式化陈述：indexEquiv_mul (P : RootPairing ι R M N) (x y : Hom P P) : indexEquiv (x *
 y) = indexEquiv x ∘ indexEquiv y
参数：P : RootPairing ι R M N；x y : Hom P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma indexEquiv_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    indexEquiv (x * y) = indexEquiv x ∘ indexEquiv y :=
  rfl

/-- The endomorphism monoid of a root pairing. -/
/-
**RootPairing.Hom._root_.RootPairing.End** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairin
g.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism monoid of a root pairing.
-/
abbrev _root_.RootPairing.End (P : RootPairing ι R M N) := Hom P P

/-- The weight space representation of endomorphisms -/
/-
**RootPairing.Hom.weightHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Hom`。
形式化陈述：weightHom (P : RootPairing ι R M N) : End P ->* (Module.End R M) where toF
un g
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight space representation of endomorphisms
-/
def weightHom (P : RootPairing ι R M N) : End P →* (Module.End R M) where
  toFun g := Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp
/-
**RootPairing.Hom.weightHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Hom
`。
形式化陈述：weightHom_injective (P : RootPairing ι R M N) : Injective (weightHom P)
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Hom.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Modu
le R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (weightHom P) := by
  intro f g hfg
  ext x
  · exact LinearMap.congr_fun hfg x
  · refine LinearEquiv.injective P.flip.toPerfPair ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.flip.toPerfPair x)
  · refine Embedding.injective P.root ?_
    simp_rw [← root_weightMap_apply]
    exact congrFun (congrArg DFunLike.coe hfg) (P.root x)

/-- The coweight space representation of endomorphisms -/
/-
**RootPairing.Hom.coweightHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Hom`。
形式化陈述：coweightHom (P : RootPairing ι R M N) : End P ->* (N ->ₗ[R] N)ᵐᵒᵖ where to
Fun g
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coweight space representation of endomorphisms
-/
def coweightHom (P : RootPairing ι R M N) : End P →* (N →ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, Module.End.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, Module.End.one_eq_id]
/-
**RootPairing.Hom.coweightHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.H
om`。
形式化陈述：coweightHom_injective (P : RootPairing ι R M N) : Injective (coweightHom P
)
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Hom.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Modu
le R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulOpposite.op_inj`：op_inj {x y : α} : op x = op y ↔ x = y
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.dualMap_dualMap_eq_iff`：∀ (R : Type u_3) (M : Type u_4) [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module
.IsReflexive R M] {…
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_iff`：eq_comp_toLinearMap_iff (f g : M₂ -
>ₛₗ[σ₂₃] M₃) : f.comp e₁₂.toLinearMap = g.comp e₁₂.toLinearMap ↔ f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.Hom.weight_coweight_transpose`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]  
 [inst_2 : _root_.Module R M] […
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Function.Embedding.apply_eq_iff_eq`：apply_eq_iff_eq {α β} (f : α ↪ β) (x
 y : α) : f x = f y ↔ x = y
· 使用引理 `RootPairing.Hom.coroot_coweightMap_apply`：coroot_coweightMap_apply {ι₂ M
₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂] (P
 : RootPairing ι R M N) (Q : R…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (coweightHom P) := by
  intro f g hfg
  ext x
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M) (σ₂₃ := .id R) P.flip.toPerfPair) hfg
    rw [← f.weight_coweight_transpose, ← g.weight_coweight_transpose] at h
    have : f.weightMap = g.weightMap := by
      have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
      refine (Module.dualMap_dualMap_eq_iff R M).mp (congrArg LinearMap.dualMap
        ((LinearEquiv.eq_comp_toLinearMap_iff f.weightMap.dualMap g.weightMap.dualMap).mp h))
    exact congrFun (congrArg DFunLike.coe this) x
  · dsimp [coweightHom] at hfg
    simp_all
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    set y := f.indexEquiv x with hy
    have : f.coweightMap (P.coroot y) = g.coweightMap (P.coroot y) := by
      exact congrFun (congrArg DFunLike.coe hfg) (P.coroot y)
    rw [coroot_coweightMap_apply, coroot_coweightMap_apply, Embedding.apply_eq_iff_eq, hy] at this
    rw [Equiv.symm_apply_apply] at this
    rw [this, Equiv.apply_symm_apply]

/-- The permutation representation of the endomorphism monoid on the root index set -/
/-
**RootPairing.Hom.indexHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Hom`。
形式化陈述：indexHom (P : RootPairing ι R M N) : End P ->* (ι ≃ ι) where toFun f
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permutation representation of the endomorphism monoid on the root index set
-/
def indexHom (P : RootPairing ι R M N) : End P →* (ι ≃ ι) where
  toFun f := Hom.indexEquiv f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end Hom

variable {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)

/-- An equivalence of root pairings is a morphism where the maps of weight and coweight spaces are
bijective.

See also `RootPairing.Equiv.toEndUnit`. -/
@[ext]
/-
**RootPairing.Equiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   {ι₂ : Type u_5} 
→                     {M₂ : Type u_6} →                       {N₂ : Type u_7} → 
                        [inst_5 : AddCommGroup M₂] →                           [
inst_6 : _root_.Module R M₂] →                             [inst_7 : AddCommGrou
p N₂] →                               [inst_8 : _root_.Module R N₂] →           
                      RootPairing ι R M N →                                   Ro
otPairing ι₂ R M₂ N₂ → Type (max (max (max (max (max u_1 u_3) u_4) u_5) u_6) u_7
)
参数：max (max (max (max (max u_1 u_3) u_4) u_5) u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of root pairings is a morphism where the maps of weight and cowei
ght spaces are
bijective.

See also `RootPairing.Equiv.toEndUnit`.
-/
protected structure Equiv extends Hom P Q where
  bijective_weightMap : Bijective weightMap
  bijective_coweightMap : Bijective coweightMap

attribute [coe] Equiv.toHom

/-- The root pairing homomorphism underlying an equivalence. -/
add_decl_doc Equiv.toHom

namespace Equiv

/-- The linear equivalence of weight spaces given by an equivalence of root pairings. -/
/-
**RootPairing.Equiv.weightEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：weightEquiv (e : RootPairing.Equiv P Q) : M ≃ₗ[R] M₂
参数：e : RootPairing.Equiv P Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.bijective_weightMap`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […

--- 原说明 ---
The linear equivalence of weight spaces given by an equivalence of root pairings
.
-/
def weightEquiv (e : RootPairing.Equiv P Q) : M ≃ₗ[R] M₂ :=
    LinearEquiv.ofBijective _ e.bijective_weightMap

@[simp]
/-
**RootPairing.Equiv.weightEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equ
iv`。
形式化陈述：weightEquiv_apply (e : RootPairing.Equiv P Q) (m : M) : weightEquiv P Q e 
m = e.toHom.weightMap m
参数：e : RootPairing.Equiv P Q；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightEquiv_apply (e : RootPairing.Equiv P Q) (m : M) :
    weightEquiv P Q e m = e.toHom.weightMap m :=
  rfl

@[simp]
/-
**RootPairing.Equiv.weightEquiv_symm_weightMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring.Equiv`。
形式化陈述：weightEquiv_symm_weightMap (e : RootPairing.Equiv P Q) (m : M) : (weightEq
uiv P Q e).symm (e.toHom.weightMap m) = m
参数：e : RootPairing.Equiv P Q；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
lemma weightEquiv_symm_weightMap (e : RootPairing.Equiv P Q) (m : M) :
    (weightEquiv P Q e).symm (e.toHom.weightMap m) = m :=
  (LinearEquiv.symm_apply_eq (weightEquiv P Q e)).mpr rfl

@[simp]
/-
**RootPairing.Equiv.weightMap_weightEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring.Equiv`。
形式化陈述：weightMap_weightEquiv_symm (e : RootPairing.Equiv P Q) (m : M₂) : e.toHom.
weightMap ((weightEquiv P Q e).symm m) = m
参数：e : RootPairing.Equiv P Q；m : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.Equiv.weightEquiv_apply`：weightEquiv_apply (e : RootPairing.
Equiv P Q) (m : M) : weightEquiv P Q e m = e.toHom.weightMap m
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
lemma weightMap_weightEquiv_symm (e : RootPairing.Equiv P Q) (m : M₂) :
    e.toHom.weightMap ((weightEquiv P Q e).symm m) = m := by
  rw [← weightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (weightEquiv P Q e) m

/-- The contravariant equivalence of coweight spaces given by an equivalence of root pairings. -/
/-
**RootPairing.Equiv.coweightEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：coweightEquiv (e : RootPairing.Equiv P Q) : N₂ ≃ₗ[R] N
参数：e : RootPairing.Equiv P Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.bijective_coweightMap`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […

--- 原说明 ---
The contravariant equivalence of coweight spaces given by an equivalence of root
 pairings.
-/
def coweightEquiv (e : RootPairing.Equiv P Q) : N₂ ≃ₗ[R] N :=
  LinearEquiv.ofBijective _ e.bijective_coweightMap

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.E
quiv`。
形式化陈述：coweightEquiv_apply (e : RootPairing.Equiv P Q) (n : N₂) : coweightEquiv P
 Q e n = e.toHom.coweightMap n
参数：e : RootPairing.Equiv P Q；n : N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightEquiv_apply (e : RootPairing.Equiv P Q) (n : N₂) :
    coweightEquiv P Q e n = e.toHom.coweightMap n :=
  rfl

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_symm_coweightMap** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.Equiv`。
形式化陈述：coweightEquiv_symm_coweightMap (e : RootPairing.Equiv P Q) (n : N₂) : (cow
eightEquiv P Q e).symm (e.toHom.coweightMap n) = n
参数：e : RootPairing.Equiv P Q；n : N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
lemma coweightEquiv_symm_coweightMap (e : RootPairing.Equiv P Q) (n : N₂) :
    (coweightEquiv P Q e).symm (e.toHom.coweightMap n) = n :=
  (LinearEquiv.symm_apply_eq (coweightEquiv P Q e)).mpr rfl

@[simp]
/-
**RootPairing.Equiv.coweightMap_coweightEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.Equiv`。
形式化陈述：coweightMap_coweightEquiv_symm (e : RootPairing.Equiv P Q) (n : N) : e.toH
om.coweightMap ((coweightEquiv P Q e).symm n) = n
参数：e : RootPairing.Equiv P Q；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.Equiv.coweightEquiv_apply`：coweightEquiv_apply (e : RootPair
ing.Equiv P Q) (n : N₂) : coweightEquiv P Q e n = e.toHom.coweightMap n
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
lemma coweightMap_coweightEquiv_symm (e : RootPairing.Equiv P Q) (n : N) :
    e.toHom.coweightMap ((coweightEquiv P Q e).symm n) = n := by
  rw [← coweightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (coweightEquiv P Q e) n

/-- The identity equivalence of a root pairing. -/
@[simps!]
/-
**RootPairing.Equiv.id** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：id (P : RootPairing ι R M N) : RootPairing.Equiv P P
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity equivalence of a root pairing.
-/
def id (P : RootPairing ι R M N) : RootPairing.Equiv P P :=
  { Hom.id P with
    bijective_weightMap := _root_.id bijective_id
    bijective_coweightMap := _root_.id bijective_id }

/-- Composition of equivalences -/
/-
**RootPairing.Equiv.comp** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommG
roup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module
 R N₂] {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing
 ι₂ R M₂ N₂} (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : RootPa
iring.Equiv P P₂
参数：g : RootPairing.Equiv P₁ P₂；f : RootPairing.Equiv P P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of equivalences
-/
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : RootPairing.Equiv P P₂ :=
  { Hom.comp g.toHom f.toHom with
    bijective_weightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp g.bijective_weightMap f.bijective_weightMap
    bijective_coweightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp f.bijective_coweightMap g.bijective_coweightMap }

@[simp]
/-
**RootPairing.Equiv.toHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [Ad
dCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [
Module R N₂] {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootP
airing ι₂ R M₂ N₂} (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : 
(Equiv.comp g f).toHom = Hom.comp g.toHom f.toHom
参数：g : RootPairing.Equiv P₁ P₂；f : RootPairing.Equiv P P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    (Equiv.comp g f).toHom = Hom.comp g.toHom f.toHom := by
  rfl

@[simp]
/-
**RootPairing.Equiv.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：id_comp {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N
₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Roo
tPairing.Equiv P Q) : comp f (id P) = f
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Equiv.toHom_comp`：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [Ad
dCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [
Module R M₂] [AddC…
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
-/
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp f (id P) = f := by
  ext x <;> simp

@[simp]
/-
**RootPairing.Equiv.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：comp_id {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N
₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Roo
tPairing.Equiv P Q) : comp (id Q) f = f
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Equiv.toHom_comp`：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [Ad
dCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [
Module R M₂] [AddC…
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Equiv.id_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
-/
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp (id Q) f = f := by
  ext x <;> simp

@[simp]
/-
**RootPairing.Equiv.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module 
R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGr
oup N₂] [Module R N₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module 
R N₃] {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing 
ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃} (h : RootPairing.Equiv P₂ P₃) (g : Roo
tPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : comp (comp h g) f = comp h 
(comp g f)
参数：h : RootPairing.Equiv P₂ P₃；g : RootPairing.Equiv P₁ P₂；f : RootPairing.Equiv
 P P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.Equiv.toHom_comp`：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [Ad
dCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [
Module R M₂] [AddC…
· 使用引理 `RootPairing.Hom.comp_assoc`：comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Typ
e*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGrou
p M₂] [Module R …
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Hom.comp_indexEquiv_apply`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
-/
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : RootPairing.Equiv P₂ P₃) (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp

/-- Equivalences form a monoid. -/
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences form a monoid.
-/
instance (P : RootPairing ι R M N) : Monoid (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P

@[simp]
/-
**RootPairing.Equiv.weightEquiv_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv
`。
形式化陈述：weightEquiv_one (P : RootPairing ι R M N) : weightEquiv (P
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightEquiv_one (P : RootPairing ι R M N) :
    weightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equ
iv`。
形式化陈述：coweightEquiv_one (P : RootPairing ι R M N) : coweightEquiv (P
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightEquiv_one (P : RootPairing ι R M N) :
    coweightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl

@[simp]
/-
**RootPairing.Equiv.toHom_one** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：toHom_one (P : RootPairing ι R M N) : (1 : RootPairing.Equiv P P).toHom = 
(1 : RootPairing.Hom P P)
参数：P : RootPairing ι R M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHom_one (P : RootPairing ι R M N) :
    (1 : RootPairing.Equiv P P).toHom = (1 : RootPairing.Hom P P) :=
  rfl

@[simp]
/-
**RootPairing.Equiv.mul_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：mul_eq_comp {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) : x * 
y = Equiv.comp x y
参数：x y : RootPairing.Equiv P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_eq_comp {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    x * y = Equiv.comp x y :=
  rfl

@[simp]
/-
**RootPairing.Equiv.weightEquiv_comp_toLin** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Equiv`。
形式化陈述：weightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv 
P P) : weightEquiv P P (Equiv.comp x y) = weightEquiv P P y ≪≫ₗ weightEquiv P P 
x
参数：x y : RootPairing.Equiv P P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Equiv.toHom_comp`：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [Ad
dCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [
Module R M₂] [AddC…
· 使用定理 `RootPairing.Hom.comp_weightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P (Equiv.comp x y) = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  ext; simp

@[simp]
/-
**RootPairing.Equiv.weightEquiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv
`。
形式化陈述：weightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) : 
weightEquiv P P x * weightEquiv P P y = weightEquiv P P y ≪≫ₗ weightEquiv P P x
参数：x y : RootPairing.Equiv P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P x * weightEquiv P P y = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  rfl

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_comp_toLin** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.Equiv`。
形式化陈述：coweightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equi
v P P) : coweightEquiv P P (Equiv.comp x y) = coweightEquiv P P x ≪≫ₗ coweightEq
uiv P P y
参数：x y : RootPairing.Equiv P P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Equiv.toHom_comp`：toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [Ad
dCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [
Module R M₂] [AddC…
· 使用定理 `RootPairing.Hom.comp_coweightMap_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coweightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P (Equiv.comp x y) = coweightEquiv P P x ≪≫ₗ coweightEquiv P P y := by
  ext; simp

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_mul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equ
iv`。
形式化陈述：coweightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) 
: coweightEquiv P P x * coweightEquiv P P y = coweightEquiv P P y ≪≫ₗ coweightEq
uiv P P x
参数：x y : RootPairing.Equiv P P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P x * coweightEquiv P P y = coweightEquiv P P y ≪≫ₗ coweightEquiv P P x := by
  rfl

/-- The inverse of a root pairing equivalence. -/
/-
**RootPairing.Equiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：symm {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] 
[Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPa
iring.Equiv P Q) : RootPairing.Equiv Q P where weightMap
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The inverse of a root pairing equivalence.
-/
def symm {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    RootPairing.Equiv Q P where
  weightMap := (weightEquiv P Q f).symm
  coweightMap := (coweightEquiv P Q f).symm
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext n m
    nth_rw 2 [show m = (weightEquiv P Q f) ((weightEquiv P Q f).symm m) by
      exact (LinearEquiv.symm_apply_eq (weightEquiv P Q f)).mp rfl]
    nth_rw 1 [show n = (coweightEquiv P Q f) ((coweightEquiv P Q f).symm n) by
      exact (LinearEquiv.symm_apply_eq (coweightEquiv P Q f)).mp rfl]
    have := f.weight_coweight_transpose
    rw [LinearMap.ext_iff₂] at this
    exact Eq.symm (this ((coweightEquiv P Q f).symm n) ((weightEquiv P Q f).symm m))
  root_weightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply]
    have := f.root_weightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv.symm i)
    simp only [comp_apply, Equiv.apply_symm_apply] at this
    simp [← this]
  coroot_coweightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply, Equiv.symm_symm]
    have := f.coroot_coweightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv i)
    simp only [comp_apply, Equiv.symm_apply_apply] at this
    simp [← this]
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (weightEquiv P Q f).symm
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (coweightEquiv P Q f).symm

@[simp]
/-
**RootPairing.Equiv.inv_weightMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：inv_weightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommG
roup N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f
 : RootPairing.Equiv P Q) : (symm P Q f).weightMap = (weightEquiv P Q f).symm
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_weightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).weightMap = (weightEquiv P Q f).symm :=
  rfl

@[simp]
/-
**RootPairing.Equiv.inv_coweightMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv
`。
形式化陈述：inv_coweightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCom
mGroup N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) 
(f : RootPairing.Equiv P Q) : (symm P Q f).coweightMap = (coweightEquiv P Q f).s
ymm
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_coweightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).coweightMap = (coweightEquiv P Q f).symm :=
  rfl

@[simp]
/-
**RootPairing.Equiv.inv_indexEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`
。
形式化陈述：inv_indexEquiv {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddComm
Group N₂] [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (
f : RootPairing.Equiv P Q) : (symm P Q f).indexEquiv = (Hom.indexEquiv f.toHom).
symm
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : RootPairing.Equiv P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_indexEquiv {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).indexEquiv = (Hom.indexEquiv f.toHom).symm :=
  rfl

/-- Equivalences form a group. -/
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences form a group.
-/
instance (P : RootPairing ι R M N) : Group (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P
  inv := symm P P
  inv_mul_cancel e := by
    ext m
    · rw [← weightEquiv_apply]
      simp
    · rw [← coweightEquiv_apply]
      simp
    · simp

/-- For finite roots systems in characteristic zero, a linear equivalence preserving roots, also
preserves coroots, and is thus an equivalence of root systems. -/
/-
**RootPairing.Equiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：mk' [IsDomain R] [CharZero R] [Module.IsTorsionFree R M₂] [Finite ι₂] (P :
 RootPairing ι R M N) [P.IsRootSystem] (Q : RootPairing ι₂ R M₂ N₂) [Q.IsRootSys
tem] (f : M ≃ₗ[R] M₂) (e : ι ≃ ι₂) (hf : forall i, f (P.root i) = Q.root (e i)) 
: P.Equiv Q where weightMap
参数：P : RootPairing ι R M N；Q : RootPairing ι₂ R M₂ N₂；f : M ≃ₗ[R] M₂；e : ι ≃ ι₂；
hf : forall i, f (P.root i) = Q.root (e i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For finite roots systems in characteristic zero, a linear equivalence preserving
 roots, also
preserves coroots, and is thus an equivalence of root systems.
-/
def mk' [IsDomain R] [CharZero R] [Module.IsTorsionFree R M₂] [Finite ι₂]
    (P : RootPairing ι R M N) [P.IsRootSystem] (Q : RootPairing ι₂ R M₂ N₂) [Q.IsRootSystem]
    (f : M ≃ₗ[R] M₂) (e : ι ≃ ι₂) (hf : ∀ i, f (P.root i) = Q.root (e i)) :
    P.Equiv Q where
  weightMap := f
  coweightMap := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := e
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp [hf]
  coroot_coweightMap := by
    let g : N ≃ₗ[R] N₂ := P.flip.toPerfPair.trans <| f.symm.dualMap.trans Q.flip.toPerfPair.symm
    suffices Q = P.map e f g by
      ext i
      rw [LinearEquiv.coe_coe, comp_apply, ← LinearEquiv.eq_symm_apply]
      conv_lhs => rw [this]
      rfl
    apply IsRootSystem.ext <;> ext
    · simp [RootPairing.map, RootPairing.map, g]
    · simp [hf, RootPairing.map, RootPairing.map]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

end Equiv

/-- The automorphism group of a root pairing. -/
/-
**RootPairing.Aut** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：Aut (P : RootPairing ι R M N)
参数：P : RootPairing ι R M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The automorphism group of a root pairing.
-/
abbrev Aut (P : RootPairing ι R M N) := (RootPairing.Equiv P P)

namespace Equiv

/-- The isomorphism between the automorphism group of a root pairing and the group of invertible
endomorphisms. -/
/-
**RootPairing.Equiv.toEndUnit** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：toEndUnit (P : RootPairing ι R M N) : Aut P ≃* (End P)ˣ where toFun f
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the automorphism group of a root pairing and the group o
f invertible
endomorphisms.
-/
def toEndUnit (P : RootPairing ι R M N) : Aut P ≃* (End P)ˣ where
  toFun f :=
  { val := f.toHom
    inv := (Equiv.symm P P f).toHom
    val_inv := by ext <;> simp
    inv_val := by ext <;> simp }
  invFun f :=
  { f.val with
    bijective_weightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.weightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul, f.inv_val, Hom.weightMap_one, LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul, f.val_inv, Hom.weightMap_one, LinearMap.id_coe]
    bijective_coweightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.coweightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul, f.val_inv, Hom.coweightMap_one, LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul, f.inv_val, Hom.coweightMap_one, LinearMap.id_coe] }
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    simp only [Equiv.mul_eq_comp, Equiv.toHom_comp]
    ext <;> simp
/-
**RootPairing.Equiv.toEndUnit_val** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：toEndUnit_val (P : RootPairing ι R M N) (g : Aut P) : (toEndUnit P g).val 
= g.toHom
参数：P : RootPairing ι R M N；g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEndUnit_val (P : RootPairing ι R M N) (g : Aut P) : (toEndUnit P g).val = g.toHom :=
  rfl
/-
**RootPairing.Equiv.toEndUnit_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`。
形式化陈述：toEndUnit_inv (P : RootPairing ι R M N) (g : Aut P) : (toEndUnit P g).inv 
= (symm P P g).toHom
参数：P : RootPairing ι R M N；g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEndUnit_inv (P : RootPairing ι R M N) (g : Aut P) :
    (toEndUnit P g).inv = (symm P P g).toHom :=
  rfl

/-- The weight space representation of automorphisms -/
@[simps]
/-
**RootPairing.Equiv.weightHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：weightHom (P : RootPairing ι R M N) : Aut P ->* (M ≃ₗ[R] M) where toFun
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight space representation of automorphisms
-/
def weightHom (P : RootPairing ι R M N) : Aut P →* (M ≃ₗ[R] M) where
  toFun := weightEquiv P P
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
/-
**RootPairing.Equiv.weightHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Equiv`。
形式化陈述：weightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) : (weightHom P
 g).toLinearMap = Hom.weightHom P g.toHom
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    (weightHom P g).toLinearMap = Hom.weightHom P g.toHom :=
  rfl
/-
**RootPairing.Equiv.weightHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.E
quiv`。
形式化陈述：weightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.weightHom
 P)
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用引理 `RootPairing.Hom.weightHom_injective`：weightHom_injective (P : RootPairin
g ι R M N) : Injective (weightHom P)
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.weightHom P) := by
  refine Injective.of_comp (f := LinearEquiv.toLinearMap) fun g g' hgg' => ?_
  let h : (weightHom P g).toLinearMap = (weightHom P g').toLinearMap := hgg' --`have` gets lint
  rw [weightHom_toLinearMap, weightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext hgg' (congrArg Hom.coweightMap h') (congrArg Hom.indexEquiv h')
  exact Hom.weightHom_injective P hgg'

@[simp]
/-
**RootPairing.Equiv.weightEquiv_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv
`。
形式化陈述：weightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) : weightEquiv P P g⁻
¹ = (weightEquiv P P g)⁻¹
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
-/
lemma weightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    weightEquiv P P g⁻¹ = (weightEquiv P P g)⁻¹ :=
  LinearEquiv.toLinearMap_inj.mp rfl

/-- The coweight space representation of automorphisms -/
@[simps]
/-
**RootPairing.Equiv.coweightHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：coweightHom (P : RootPairing ι R M N) : Aut P ->* (N ≃ₗ[R] N)ᵐᵒᵖ where toF
un g
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coweight space representation of automorphisms
-/
def coweightHom (P : RootPairing ι R M N) : Aut P →* (N ≃ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (coweightEquiv P P g)
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff]
    exact LinearEquiv.toLinearMap_inj.mp rfl
  map_mul' := by
    simp only [mul_eq_comp, coweightEquiv_comp_toLin]
    exact fun x y ↦ rfl
/-
**RootPairing.Equiv.coweightHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.Equiv`。
形式化陈述：coweightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) : (MulOpposi
te.unop (coweightHom P g)).toLinearMap = MulOpposite.unop (Hom.coweightHom P g.t
oHom)
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    (MulOpposite.unop (coweightHom P g)).toLinearMap =
      MulOpposite.unop (Hom.coweightHom P g.toHom) :=
  rfl
/-
**RootPairing.Equiv.coweightHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Equiv`。
形式化陈述：coweightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.coweigh
tHom P)
参数：P : RootPairing ι R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.Equiv.coweightHom_apply`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.Hom.coweightHom_injective`：coweightHom_injective (P : RootPa
iring ι R M N) : Injective (coweightHom P)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulOpposite.unop_inj`：unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y
· 使用引理 `RootPairing.Equiv.coweightHom_toLinearMap`：coweightHom_toLinearMap {P : 
RootPairing ι R M N} (g : Aut P) : (MulOpposite.unop (coweightHom P g)).toLinear
Map = MulOpposite.unop (Hom.cow…
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
-/
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.coweightHom P) := by
  refine Injective.of_comp (f := fun a => MulOpposite.op a) fun g g' hgg' => ?_
  have h : (MulOpposite.unop (coweightHom P g)).toLinearMap =
      (MulOpposite.unop (coweightHom P g')).toLinearMap := by
    simp_all
  rw [coweightHom_toLinearMap, coweightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext (congrArg Hom.weightMap h') h (congrArg Hom.indexEquiv h')
  apply Hom.coweightHom_injective P
  exact MulOpposite.unop_inj.mp h
/-
**RootPairing.Equiv.coweightHom_op** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`
。
形式化陈述：coweightHom_op {P : RootPairing ι R M N} (g : Aut P) : MulOpposite.unop (c
oweightHom P g) = coweightEquiv P P g
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coweightHom_op {P : RootPairing ι R M N} (g : Aut P) :
    MulOpposite.unop (coweightHom P g) = coweightEquiv P P g :=
  rfl

@[simp]
/-
**RootPairing.Equiv.coweightEquiv_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equ
iv`。
形式化陈述：coweightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) : coweightEquiv P 
P g⁻¹ = (coweightEquiv P P g)⁻¹
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
-/
lemma coweightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    coweightEquiv P P g⁻¹ = (coweightEquiv P P g)⁻¹ :=
  LinearEquiv.toLinearMap_inj.mp rfl

/-- The permutation representation of the automorphism group on the root index set -/
@[simps]
/-
**RootPairing.Equiv.indexHom** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：indexHom (P : RootPairing ι R M N) : Aut P ->* (ι ≃ ι) where toFun g
参数：P : RootPairing ι R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permutation representation of the automorphism group on the root index set
-/
def indexHom (P : RootPairing ι R M N) : Aut P →* (ι ≃ ι) where
  toFun g := g.toHom.indexEquiv
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
/-
**RootPairing.Equiv.indexEquiv_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`
。
形式化陈述：indexEquiv_inv {P : RootPairing ι R M N} (g : Aut P) : (g⁻¹).toHom.indexEq
uiv = (indexHom P g)⁻¹
参数：g : Aut P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma indexEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    (g⁻¹).toHom.indexEquiv = (indexHom P g)⁻¹ :=
  rfl

/-- The automorphism of a root pairing given by a reflection. -/
/-
**RootPairing.Equiv.reflection** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Equiv`。
形式化陈述：reflection (P : RootPairing ι R M N) (i : ι) : Aut P where weightMap
参数：P : RootPairing ι R M N；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The automorphism of a root pairing given by a reflection.
-/
def reflection (P : RootPairing ι R M N) (i : ι) : Aut P where
  weightMap := P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflectionPerm i
  weight_coweight_transpose := by
    ext f x; simpa [reflection_apply, coreflection_apply] using mul_comm ..
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.reflection i)
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.coreflection i)

@[simp]
/-
**RootPairing.Equiv.reflection_weightEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Equiv`。
形式化陈述：reflection_weightEquiv (P : RootPairing ι R M N) (i : ι) : (reflection P i
).weightEquiv = P.reflection i
参数：P : RootPairing ι R M N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
-/
lemma reflection_weightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).weightEquiv = P.reflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
/-
**RootPairing.Equiv.reflection_coweightEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.Equiv`。
形式化陈述：reflection_coweightEquiv (P : RootPairing ι R M N) (i : ι) : (reflection P
 i).coweightEquiv = P.coreflection i
参数：P : RootPairing ι R M N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
-/
lemma reflection_coweightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).coweightEquiv = P.coreflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
/-
**RootPairing.Equiv.reflection_indexEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Equiv`。
形式化陈述：reflection_indexEquiv (P : RootPairing ι R M N) (i : ι) : (reflection P i)
.indexEquiv = P.reflectionPerm i
参数：P : RootPairing ι R M N；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reflection_indexEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).indexEquiv = P.reflectionPerm i :=
  rfl

@[simp]
/-
**RootPairing.Equiv.reflection_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Equiv`
。
形式化陈述：reflection_inv (P : RootPairing ι R M N) (i : ι) : (reflection P i)⁻¹ = (r
eflection P i)
参数：P : RootPairing ι R M N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Equiv.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_.Mo
dule R M} {…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.Equiv.weightEquiv_inv`：weightEquiv_inv {P : RootPairing ι R 
M N} (g : Aut P) : weightEquiv P P g⁻¹ = (weightEquiv P P g)⁻¹
· 使用引理 `RootPairing.Equiv.reflection_weightEquiv`：reflection_weightEquiv (P : Ro
otPairing ι R M N) (i : ι) : (reflection P i).weightEquiv = P.reflection i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.Equiv.coweightEquiv_inv`：coweightEquiv_inv {P : RootPairing 
ι R M N} (g : Aut P) : coweightEquiv P P g⁻¹ = (coweightEquiv P P g)⁻¹
· 使用引理 `RootPairing.Equiv.reflection_coweightEquiv`：reflection_coweightEquiv (P 
: RootPairing ι R M N) (i : ι) : (reflection P i).coweightEquiv = P.coreflection
 i
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `RootPairing.Equiv.indexHom_apply`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用引理 `RootPairing.reflectionPerm_inv`：reflectionPerm_inv : (P.reflectionPerm i
)⁻¹ = P.reflectionPerm i
-/
lemma reflection_inv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i)⁻¹ = (reflection P i) := by
  refine Equiv.ext ?_ ?_ ?_
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← weightEquiv_apply])
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← coweightEquiv_apply])
  · exact _root_.Equiv.ext (fun j => by simp)
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction P.Aut M where
  smul w x := weightHom P w x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show weightHom P w 0 = 0 by simp
  smul_add w x y := show weightHom P w (x + y) = weightHom P w x + weightHom P w y by simp
/-
**RootPairing.Equiv.reflection_smul** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Equiv
`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N) (i : ι)   (x :
 M), RootPairing.Equiv.reflection P i • x = (P.reflection i) x
参数：P : RootPairing ι R M N；i : ι；x : M；P.reflection i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma reflection_smul (i : ι) (x : M) : Equiv.reflection P i • x = P.reflection i x := rfl
/-
**RootPairing.Equiv.root_indexEquiv_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `RootPairi
ng.Equiv`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N) (i : ι)   (g :
 P.Aut), P.root ((↑g).indexEquiv i) = g • P.root i
参数：P : RootPairing ι R M N；i : ι；g : P.Aut；(↑g).indexEquiv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `RootPairing.Hom.root_weightMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
@[simp] lemma root_indexEquiv_eq_smul (i : ι) (g : P.Aut) :
    P.root (g.indexEquiv i) = g • P.root i := by
  simpa using! (congr_fun g.root_weightMap i).symm

open MulOpposite in
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction P.Autᵐᵒᵖ N where
  smul w x := unop (coweightHom P (unop w)) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show unop (coweightHom P (unop w)) 0 = 0 by simp
  smul_add w x y := by
    change unop (coweightHom P _) (x + y) = unop (coweightHom P _) x + unop (coweightHom P _) y
    simp
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass P.Aut R M where
  smul_comm w t x := show weightHom P w (t • x) = t • weightHom P w x by simp

open MulOpposite in
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass P.Autᵐᵒᵖ R N where
  smul_comm w t x := by
    change unop (coweightHom P (unop w)) (t • x) = t • unop (coweightHom P (unop w)) x
    simp
/-
**RootPairing.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction P.Aut ι where
  smul w i := Equiv.indexHom P w i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end Equiv

end RootPairing

