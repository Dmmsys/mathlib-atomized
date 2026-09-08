/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Lie.Cochain

/-!
# Extensions of Lie algebras

This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

Because our sign convention for differentials is opposite that of Chevalley-Eilenberg, there is a
change of signs in the "action" part of the Lie bracket.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.
* `LieAlgebra.ofTwoCocycle`: The Lie algebra built from a direct product, but whose bracket product
  is sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle`: The Lie algebra extension constructed from a 2-cocycle.
* `LieAlgebra.Extension.ringModuleOf`: Given an extension whose kernel is abelian, we obtain a Lie
  action of the target on the kernel.
* `LieAlgebra.Extension.twoCocycle`: The 2-cocycle attached to an extension with a linear section.
* `LieAlgebra.Extension.oneCochainOfTwoSplitting`: A 1-cochain attached to a pair of linear sections
  of an extension.

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

@[expose] public section

open Function

namespace LieAlgebra

variable {R N L M : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
/-
**LieAlgebra.IsExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：{R : Type u_1} →   {N : Type u_2} →     {L : Type u_3} →       {M : Type u
_4} →         [inst : CommRing R] →           [inst_1 : LieRing L] →            
 [inst_2 : LieAlgebra R L] →               [inst_3 : LieRing N] →               
  [inst_4 : LieAlgebra R N] →                   [inst_5 : LieRing M] → [inst_6 :
 LieAlgebra R M] → (N →ₗ⁅R⁆ L) → (L →ₗ⁅R⁆ M) → Prop
参数：N →ₗ⁅R⁆ L；L →ₗ⁅R⁆ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of two Lie algebra homomorphisms is an extension if it is short exact
.
-/
class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker
/-
**LieAlgebra._root_.LieHom.range_eq_ker_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LieHom.range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Exact i p :=
  ⟨fun h x ↦ by simp [← LieHom.coe_range, h], fun h ↦ (p.ker.toLieSubalgebra.ext i.range h).symm⟩

/-- The equivalence from the kernel of the projection. -/
/-
**LieAlgebra.IsExtension.kerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsE
xtension`。
形式化陈述：{R : Type u_1} →   {N : Type u_2} →     {L : Type u_3} →       {M : Type u
_4} →         [inst : CommRing R] →           [inst_1 : LieRing L] →            
 [inst_2 : LieAlgebra R L] →               [inst_3 : LieRing N] →               
  [inst_4 : LieAlgebra R N] →                   [inst_5 : LieRing M] →          
           [inst_6 : LieAlgebra R M] →                       (i : N →ₗ⁅R⁆ L) → (
p : L →ₗ⁅R⁆ M) → [LieAlgebra.IsExtension i p] → ↥p.ker ≃ₗ[R] ↥i.range
参数：i : N →ₗ⁅R⁆ L；p : L →ₗ⁅R⁆ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence from the kernel of the projection.
-/
def IsExtension.kerEquivRange (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) [IsExtension i p] :
    p.ker ≃ₗ[R] i.range :=
  .ofEq (R := R) (M := L) p.ker i.range <| by simp [exact (i := i) (p := p)]

variable (R N M) in
/-- The type of all Lie extensions of `M` by `N`.  That is, short exact sequences of `R`-Lie algebra
homomorphisms `0 → N → L → M → 0` where `R`, `M`, and `N` are fixed. -/
/-
**LieAlgebra.Extension** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) →   (N : Type u_2) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing N] →           [LieAlgebra R N] → [inst_3 :
 LieRing M] → [LieAlgebra R M] → Type (max (max (max u_1 u_2) u_4) (u_5 + 1))
参数：max (max u_1 u_2) u_4；u_5 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of all Lie extensions of `M` by `N`.  That is, short exact sequences of
 `R`-Lie algebra
homomorphisms `0 → N → L → M → 0` where `R`, `M`, and `N` are fixed.
-/
structure Extension where
  /-- The middle object in the sequence. -/
  L : Type*
  /-- `L` is a Lie ring. -/
  instLieRing : LieRing L
  /-- `L` is a Lie algebra over `R`. -/
  instLieAlgebra : LieAlgebra R L
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L →ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (E : Extension R M N) : LieRing E.L := E.instLieRing
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (E : Extension R M N) : LieAlgebra R E.L := E.instLieAlgebra

/-- The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension` -/
/-
**LieAlgebra.IsExtension.extension** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsExten
sion`。
形式化陈述：{R : Type u_1} →   {N : Type u_2} →     {L : Type u_3} →       {M : Type u
_4} →         [inst : CommRing R] →           [inst_1 : LieRing L] →            
 [inst_2 : LieAlgebra R L] →               [inst_3 : LieRing N] →               
  [inst_4 : LieAlgebra R N] →                   [inst_5 : LieRing M] →          
           [inst_6 : LieAlgebra R M] →                       {i : N →ₗ⁅R⁆ L} → {
p : L →ₗ⁅R⁆ M} → LieAlgebra.IsExtension i p → LieAlgebra.Extension R N M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension`
-/
@[simps] def IsExtension.extension {i : N →ₗ⁅R⁆ L} {p : L →ₗ⁅R⁆ M} (h : IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

/-- A surjective Lie algebra homomorphism yields an extension. -/
/-
**LieAlgebra.isExtension_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：isExtension_of_surjective (f : L ->ₗ⁅R⁆ M) (hf : Surjective f) : IsExtensi
on f.ker.incl f where ker_eq_bot
参数：f : L ->ₗ⁅R⁆ M；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieIdeal.ker_incl`：ker_incl : I.incl.ker = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
· 使用定理 `LieIdeal.incl_range`：incl_range : I.incl.range = I

--- 原说明 ---
A surjective Lie algebra homomorphism yields an extension.
-/
lemma isExtension_of_surjective (f : L →ₗ⁅R⁆ M) (hf : Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

end IsExtension

namespace Extension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-
**LieAlgebra.Extension.incl_apply_mem_ker** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.
Extension`。
形式化陈述：incl_apply_mem_ker (E : Extension R M L) (x : M) : E.incl x in E.proj.ker
参数：E : Extension R M L；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Exact.apply_apply_eq_zero`：∀ {M : Type u_2} {N : Type u_4} {P :
 Type u_6} {f : M → N} {g : N → P} [inst : Zero P],   Function.Exact f g → ∀ (x 
: M), g (f x) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieHom.range_eq_ker_iff`：∀ {R : Type u_1} {N : Type u_2} {L : Type u_3} 
{M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : LieAlgebra R
 L] [inst_3 :…
· 使用定理 `LieAlgebra.IsExtension.exact`：∀ {R : Type u_1} {N : Type u_2} {L : Type 
u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L}   {inst_2 : LieAlge
bra R L} {inst_3 :…
· 使用定理 `LieAlgebra.Extension.IsExtension`：∀ {R : Type u_1} {N : Type u_2} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing N] [inst_2 : LieAlgebra R N]   [i
nst_3 : LieRing M] [in…
-/
lemma incl_apply_mem_ker (E : Extension R M L) (x : M) :
    E.incl x ∈ E.proj.ker :=
  Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x
/-
**LieAlgebra.Extension.proj_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Extension
`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing M] [inst_4 : LieAlge
bra R M] (E : LieAlgebra.Extension R M L) (x : M), E.proj (E.incl x) = 0
参数：E : LieAlgebra.Extension R M L；x : M；E.incl x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
· 使用引理 `LieAlgebra.Extension.incl_apply_mem_ker`：incl_apply_mem_ker (E : Extensi
on R M L) (x : M) : E.incl x in E.proj.ker
-/
@[simp] lemma proj_incl (E : Extension R M L) (x : M) :
    E.proj (E.incl x) = 0 :=
  LieHom.mem_ker.mp (incl_apply_mem_ker E x)
/-
**LieAlgebra.Extension.incl_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Exte
nsion`。
形式化陈述：incl_injective (E : Extension R M L) : Injective E.incl
参数：E : Extension R M L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieHom.ker_eq_bot`：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
· 使用定理 `LieAlgebra.IsExtension.ker_eq_bot`：∀ {R : Type u_1} {N : Type u_2} {L : 
Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L}   {inst_2 : Li
eAlgebra R L} {inst_3 :…
· 使用定理 `LieAlgebra.Extension.IsExtension`：∀ {R : Type u_1} {N : Type u_2} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing N] [inst_2 : LieAlgebra R N]   [i
nst_3 : LieRing M] [in…
-/
lemma incl_injective (E : Extension R M L) :
    Injective E.incl :=
  (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot
/-
**LieAlgebra.Extension.proj_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Ext
ension`。
形式化陈述：proj_surjective (E : Extension R M L) : Surjective E.proj
参数：E : Extension R M L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
· 使用定理 `LieAlgebra.IsExtension.range_eq_top`：∀ {R : Type u_1} {N : Type u_2} {L 
: Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L}   {inst_2 : 
LieAlgebra R L} {inst_3 :…
· 使用定理 `LieAlgebra.Extension.IsExtension`：∀ {R : Type u_1} {N : Type u_2} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing N] [inst_2 : LieAlgebra R N]   [i
nst_3 : LieRing M] [in…
-/
lemma proj_surjective (E : Extension R M L) :
    Surjective E.proj :=
  (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

end Extension

section Algebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

open LieModule.Cohomology

/-- A one-field structure giving a type synonym for a direct product. We use this to describe an
alternative Lie algebra structure on the product, where the bracket is shifted by a 2-cocycle. -/
/-
**LieAlgebra.ofTwoCocycle** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：{R : Type u_5} →   {L : Type u_6} →     {M : Type u_7} →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] →                   [inst_6 : 
LieModule R L M] → ↥(LieModule.Cohomology.twoCocycle R L M) → Type (max u_6 u_7)
参数：LieModule.Cohomology.twoCocycle R L M；max u_6 u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A one-field structure giving a type synonym for a direct product. We use this to
 describe an
alternative Lie algebra structure on the product, where the bracket is shifted b
y a 2-cocycle.
-/
structure ofTwoCocycle {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M]
    (c : twoCocycle R L M) where
  /-- The underlying type. -/
  carrier : L × M

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (c : twoCocycle R L M)

/-- An equivalence between the direct product and the corresponding one-field structure. This is
used to transfer the additive and scalar-multiple structure on the direct product to the type
synonym. -/
/-
**LieAlgebra.ofProd** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：ofProd : L × M ≃ ofTwoCocycle c where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the direct product and the corresponding one-field struct
ure. This is
used to transfer the additive and scalar-multiple structure on the direct produc
t to the type
synonym.
-/
def ofProd : L × M ≃ ofTwoCocycle c where
  toFun a := ⟨a⟩
  invFun a := a.carrier

-- transport instances along the equivalence
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (ofTwoCocycle c) := (ofProd c).symm.addCommGroup
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (ofTwoCocycle c) := (ofProd c).symm.module R
/-
**LieAlgebra.of_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)), (LieAlgebra.ofProd c) 0 = 0
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
@[simp] lemma of_zero : ofProd c (0 : L × M) = 0 := rfl
/-
**LieAlgebra.of_add** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (x y : L × M),   (LieAlgebra.ofProd c)
 (x + y) = (LieAlgebra.ofProd c) x + (LieAlgebra.ofProd c) y
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；x y : L × M；LieAlgebra.ofProd c；
x + y；LieAlgebra.ofProd c；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
@[simp] lemma of_add (x y : L × M) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
/-
**LieAlgebra.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (r : R) (x : L × M),   (LieAlgebra.ofP
rod c) (r • x) = r • (LieAlgebra.ofProd c) x
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；r : R；x : L × M；LieAlgebra.ofPro
d c；r • x；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
@[simp] lemma of_smul (r : R) (x : L × M) : (ofProd c) (r • x) = r • ofProd c x := rfl
/-
**LieAlgebra.of_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)), (LieAlgebra.ofProd c).symm 0 = 0
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycle c) = 0 := rfl
/-
**LieAlgebra.of_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (x y : LieAlgebra.ofTwoCocycle c),   (
LieAlgebra.ofProd c).symm (x + y) = (LieAlgebra.ofProd c).symm x + (LieAlgebra.o
fProd c).symm y
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；x y : LieAlgebra.ofTwoCocycle c；
LieAlgebra.ofProd c；x + y；LieAlgebra.ofProd c；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma of_symm_add (x y : ofTwoCocycle c) :
    (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
/-
**LieAlgebra.of_symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (r : R) (x : LieAlgebra.ofTwoCocycle c
),   (LieAlgebra.ofProd c).symm (r • x) = r • (LieAlgebra.ofProd c).symm x
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；r : R；x : LieAlgebra.ofTwoCocycl
e c；LieAlgebra.ofProd c；r • x；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycle c) :
    (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl
/-
**LieAlgebra.of_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (n : ℕ) (x : L × M),   (LieAlgebra.ofP
rod c) (n • x) = n • (LieAlgebra.ofProd c) x
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；n : ℕ；x : L × M；LieAlgebra.ofPro
d c；n • x；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
@[simp] lemma of_nsmul (n : ℕ) (x : L × M) : (ofProd c) (n • x) = n • (ofProd c) x := rfl
/-
**LieAlgebra.of_symm_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (c : 
↥(LieModule.Cohomology.twoCocycle R L M)) (n : ℕ) (x : LieAlgebra.ofTwoCocycle c
),   (LieAlgebra.ofProd c).symm (n • x) = n • (LieAlgebra.ofProd c).symm x
参数：c : ↥(LieModule.Cohomology.twoCocycle R L M)；n : ℕ；x : LieAlgebra.ofTwoCocycl
e c；LieAlgebra.ofProd c；n • x；LieAlgebra.ofProd c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma of_symm_nsmul (n : ℕ) (x : ofTwoCocycle c) :
    (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (ofTwoCocycle c) where
  bracket x y :=
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ofProd c (⁅x₁, y₁⁆, (c : L →ₗ[R] L →ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero, c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1, ((ofProd c).symm z).1⁆,
      ← twoCochain_skew _ _ ⁅((ofProd c).symm y).1, ((ofProd c).symm z).1⁆, eq_sub_iff_add_eq,
      zero_add, neg_eq_iff_eq_neg] at this
    rw [this]
    abel
/-
**LieAlgebra.bracket_ofTwoCocycle** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) : letI 
x₁
参数：x y : ofTwoCocycle c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) :
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ⁅x, y⁆ = ofProd c (⁅x₁, y₁⁆, (c : L →ₗ[R] L →ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieAlgebra R (ofTwoCocycle c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

/-- An equivalence of extended Lie algebras induced by translation by a coboundary. -/
@[simps]
/-
**LieAlgebra.LieEquiv.ofCoboundary** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.LieEqui
v`。
形式化陈述：{R : Type u_1} →   {L : Type u_3} →     {M : Type u_4} →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] →                   [inst_6 : 
LieModule R L M] →                     (c c' : ↥(LieModule.Cohomology.twoCocycle
 R L M)) →                       (x : LieModule.Cohomology.oneCochain R L M) →  
                       ↑c' = ↑c + (LieModule.Cohomology.d₁₂ R L M) x →          
                 LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ LieAlgebra.ofTwoCocycle c'
参数：c c' : ↥(LieModule.Cohomology.twoCocycle R L M)；x : LieModule.Cohomology.oneC
ochain R L M；LieModule.Cohomology.d₁₂ R L M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence of extended Lie algebras induced by translation by a coboundary.
-/
def LieEquiv.ofCoboundary (c' : twoCocycle R L M) (x : oneCochain R L M)
    (h : c' = c + d₁₂ R L M x) :
    ofTwoCocycle c ≃ₗ⁅R⁆ ofTwoCocycle c' where
  toFun y :=
    letI z := (ofProd c).symm y
    ofProd c' (z.1, z.2 - x z.1)
  invFun z :=
    letI y := (ofProd c').symm z
    ofProd c (y.1, y.2 + x y.1)
  map_add' _ _ := by simp [← of_add]; abel
  map_smul' := by simp [← of_smul, smul_sub]
  map_lie' := ((ofProd c').eq_symm_apply).1 <| by simp [bracket_ofTwoCocycle, h]; abel
  left_inv y := by simp
  right_inv z := by simp

end Algebra

namespace Extension

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

section TwoCocycle

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

/-- The extension of Lie algebras defined by a 2-cocycle. -/
/-
**LieAlgebra.Extension.ofTwoCocycle** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extens
ion`。
形式化陈述：ofTwoCocycle : Extension R M L where L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The extension of Lie algebras defined by a 2-cocycle.
-/
def ofTwoCocycle : Extension R M L where
  L := LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [trivial_lie_zero, bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

/-- The Lie algebra isomorphism given by the type synonym. -/
/-
**LieAlgebra.Extension.ofAlg** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extension`。
形式化陈述：ofAlg : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie algebra isomorphism given by the type synonym.
-/
def ofAlg : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L := LieEquiv.refl
/-
**LieAlgebra.Extension.bracket** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Extension`。
形式化陈述：bracket (x y : (ofTwoCocycle c).L) : ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (
ofAlg c).symm y⁆
参数：x y : (ofTwoCocycle c).L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma bracket (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ :=
  rfl

@[simp]
/-
**LieAlgebra.Extension.ofTwoCocycle_incl_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.Extension`。
形式化陈述：ofTwoCocycle_incl_apply (x : M) : (ofTwoCocycle c).incl x = ⟨(0, x)⟩
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma ofTwoCocycle_incl_apply (x : M) : (ofTwoCocycle c).incl x = ⟨(0, x)⟩ :=
  rfl

@[simp]
/-
**LieAlgebra.Extension.ofTwoCocycle_proj_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.Extension`。
形式化陈述：ofTwoCocycle_proj_apply (x : (ofTwoCocycle c).L) : (ofTwoCocycle c).proj x
 = x.carrier.1
参数：x : (ofTwoCocycle c).L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma ofTwoCocycle_proj_apply (x : (ofTwoCocycle c).L) : (ofTwoCocycle c).proj x = x.carrier.1 :=
  rfl

end TwoCocycle

/-
**LieAlgebra.Extension.lie_incl_mem_ker** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Ex
tension`。
形式化陈述：lie_incl_mem_ker {E : Extension R M L} (x : E.L) (y : M) : ⁅x, E.incl y⁆ i
n E.proj.ker
参数：x : E.L；y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `LieAlgebra.Extension.proj_incl`：∀ {R : Type u_1} {L : Type u_3} {M : Typ
e u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [ins
t_3 : LieRing M] [in…
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
-/
lemma lie_incl_mem_ker {E : Extension R M L} (x : E.L) (y : M) :
    ⁅x, E.incl y⁆ ∈ E.proj.ker := by
  rw [LieHom.mem_ker, LieHom.map_lie, proj_incl, lie_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-- The Lie algebra isomorphism from the kernel of an extension to the kernel of the projection. -/
/-
**LieAlgebra.Extension.toKer** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extension`。
形式化陈述：toKer (E : Extension R M L) : M ≃ₗ⁅R⁆ E.proj.ker where toFun m
参数：E : Extension R M L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieAlgebra.Extension.incl_apply_mem_ker`：incl_apply_mem_ker (E : Extensi
on R M L) (x : M) : E.incl x in E.proj.ker
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `LieAlgebra.Extension.incl_injective`：incl_injective (E : Extension R M L
) : Injective E.incl
· 使用定理 `LieAlgebra.Extension.IsExtension`：∀ {R : Type u_1} {N : Type u_2} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing N] [inst_2 : LieAlgebra R N]   [i
nst_3 : LieRing M] [in…

--- 原说明 ---
The Lie algebra isomorphism from the kernel of an extension to the kernel of the
 projection.
-/
noncomputable def toKer (E : Extension R M L) :
    M ≃ₗ⁅R⁆ E.proj.ker where
  toFun m := ⟨E.incl m, E.incl_apply_mem_ker m⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {x y} := by ext; simp [← LieHom.map_lie]
  invFun := (Equiv.ofInjective E.incl E.incl_injective).symm ∘ E.IsExtension.kerEquivRange
  left_inv _ := by
    simp [IsExtension.kerEquivRange, Equiv.symm_apply_eq]
    rfl
  right_inv x := by simpa [Subtype.ext_iff] using! Equiv.apply_ofInjective_symm E.incl_injective _

set_option backward.isDefEq.respectTransparency.types false in
/-
**LieAlgebra.Extension.lie_toKer_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Ext
ension`。
形式化陈述：∀ {R : Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing M] [inst_4 : LieAlge
bra R M] (E : LieAlgebra.Extension R M L) (x : M) (y : E.L),   ⁅y, ↑(E.toKer x)⁆
 = ⁅y, E.incl x⁆
参数：E : LieAlgebra.Extension R M L；x : M；y : E.L；E.toKer x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lie_toKer_apply (E : Extension R M L) (x : M) (y : E.L) :
    ⁅y, (E.toKer x : E.L)⁆ = ⁅y, E.incl x⁆ := by
  rfl
/-
**LieAlgebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLieAbelian M] (E : Extension R M L) : IsLieAbelian E.proj.ker :=
  (lie_abelian_iff_equiv_lie_abelian E.toKer.symm).mpr inferInstance

/-- Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` gets an `L`-module
structure. We do not make this an instance, because we may have to work with more than one
extension. -/
@[simps, instance_reducible]
/-
**LieAlgebra.Extension.ringModuleOf** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extens
ion`。
形式化陈述：ringModuleOf [IsLieAbelian M] (E : Extension R M L) : LieRingModule L M wh
ere bracket x y
参数：E : Extension R M L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` get
s an `L`-module
structure. We do not make this an instance, because we may have to work with mor
e than one
extension.
-/
noncomputable def ringModuleOf [IsLieAbelian M] (E : Extension R M L) : LieRingModule L M where
  bracket x y := E.toKer.symm ⁅E.proj_surjective.hasRightInverse.choose x, E.toKer y⁆
  add_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    rw [← map_add, ← add_lie, eq_comm, EquivLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie]
    exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
  lie_add x m n := by simp [← map_add, ← lie_add]
  leibniz_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    have aux (z : E.proj.ker) : ⁅⁅h.choose x, h.choose y⁆, z⁆ = ⁅h.choose ⁅x, y⁆, z⁆ := by
      rw [← sub_eq_zero, ← sub_lie]
      exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ z
    rw [← map_add, EquivLike.apply_eq_iff_eq, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply,
      leibniz_lie, aux]
/-
**LieAlgebra.Extension.ringModuleOf_bracket_proj** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra.Extension`。
形式化陈述：ringModuleOf_bracket_proj [IsLieAbelian M] (E : Extension R M L) (y : M) (
z : E.L) : letI
参数：E : Extension R M L；y : M；z : E.L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用引理 `LieAlgebra.Extension.proj_surjective`：proj_surjective (E : Extension R M
 L) : Surjective E.proj
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.IsExtension.exact`：∀ {R : Type u_1} {N : Type u_2} {L : Type 
u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L}   {inst_2 : LieAlge
bra R L} {inst_3 :…
· 使用定理 `LieAlgebra.Extension.IsExtension`：∀ {R : Type u_1} {N : Type u_2} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing N] [inst_2 : LieAlgebra R N]   [i
nst_3 : LieRing M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieAlgebra.Extension.ringModuleOf_bracket`：∀ {R : Type u_1} {L : Type u_
3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra 
R L]   [inst_3 : LieRing M] [in…
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_lie`：sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `LieSubmodule.coe_bracket`：coe_bracket (x : L) (m : N) : (↑⁅x, m⁆ : M) = 
⁅x, ↑m⁆
· 使用定理 `LieAlgebra.Extension.lie_toKer_apply`：∀ {R : Type u_1} {L : Type u_3} {M
 : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] 
  [inst_3 : LieRing M] [in…
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `LieHom.coe_toLinearMap`：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->
ₗ[R] L₂) = f
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 31 条，此处仅展示前 30 条）
-/
lemma ringModuleOf_bracket_proj [IsLieAbelian M] (E : Extension R M L) (y : M) (z : E.L) :
    letI := E.ringModuleOf
    ⁅E.proj z, y⁆ = E.toKer.symm ⁅z, E.toKer y⁆ := by
  obtain ⟨x, hx⟩ : E.proj_surjective.hasRightInverse.choose (E.proj z) - z ∈ E.incl.range := by
    rw [E.IsExtension.exact]
    change _ ∈ E.proj.ker
    simp [E.proj_surjective.hasRightInverse.choose_spec (E.proj z)]
  rw [ringModuleOf_bracket, EmbeddingLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie,
    Subtype.ext_iff, LieSubmodule.coe_bracket, lie_toKer_apply, ZeroMemClass.coe_zero, ← hx,
    LieHom.coe_toLinearMap, ← LieHom.map_lie, trivial_lie_zero M M x y, map_zero]

/-- Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` gets an `R`-linear
`L`-module structure. We do not make this an instance, because we may have to work with more than
one extension. -/
/-
**LieAlgebra.Extension.lieModuleOf** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Extensi
on`。
形式化陈述：lieModuleOf [IsLieAbelian M] (E : Extension R M L) : letI
参数：E : Extension R M L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用引理 `LieAlgebra.Extension.proj_surjective`：proj_surjective (E : Extension R M
 L) : Surjective E.proj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Extension.ringModuleOf_bracket`：∀ {R : Type u_1} {L : Type u_
3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra 
R L]   [inst_3 : LieRing M] [in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LieEquiv.instLinearEquivClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w
} [inst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : Li
eAlgebra R L₁] [ins…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `EquivLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : E) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_lie`：sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieAlgebra.Extension.instIsLieAbelianSubtypeLMemLieIdealKerProj`：∀ {R : 
Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L]
 [inst_2 : LieAlgebra R L]   [inst_3 : LieRing M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆

--- 原说明 ---
Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` get
s an `R`-linear
`L`-module structure. We do not make this an instance, because we may have to wo
rk with more than
one extension.
-/
lemma lieModuleOf [IsLieAbelian M] (E : Extension R M L) :
    letI := E.ringModuleOf
    LieModule R L M := by
  let := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket, ringModuleOf_bracket, ← map_smul, ← smul_lie,
          EquivLike.apply_eq_iff_eq, ← sub_eq_zero, ← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }
/-
**LieAlgebra.Extension.toKer_bracket** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Exten
sion`。
形式化陈述：toKer_bracket [IsLieAbelian M] (E : Extension R M L) (x : E.proj.ker) (y :
 L) : letI
参数：E : Extension R M L；x : E.proj.ker；y : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用引理 `LieAlgebra.Extension.proj_surjective`：proj_surjective (E : Extension R M
 L) : Surjective E.proj
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieEquiv.apply_symm_apply`：apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toKer_bracket [IsLieAbelian M] (E : Extension R M L) (x : E.proj.ker) (y : L) :
    letI := E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp
/-
**LieAlgebra.Extension.lie_apply_proj_of_leftInverse_eq** 是 Mathlib 中的一个引理，位于命名空
间 `LieAlgebra.Extension`。
形式化陈述：lie_apply_proj_of_leftInverse_eq [IsLieAbelian M] (E : Extension R M L) {s
 : L ->ₗ[R] E.L} (hs : LeftInverse E.proj s) (x : E.L) (y : E.proj.ker) : ⁅s (E.
proj x), y⁆ = ⁅x, y⁆
参数：E : Extension R M L；hs : LeftInverse E.proj s；x : E.L；y : E.proj.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_lie`：sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieAlgebra.Extension.instIsLieAbelianSubtypeLMemLieIdealKerProj`：∀ {R : 
Type u_1} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L]
 [inst_2 : LieAlgebra R L]   [inst_3 : LieRing M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `Function.LeftInverse.eq`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f 
: α → β}, Function.LeftInverse g f → ∀ (x : α), g (f x) = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_apply_proj_of_leftInverse_eq [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x : E.L) (y : E.proj.ker) :
    ⁅s (E.proj x), y⁆ = ⁅x, y⁆ := by
  rw [← sub_eq_zero, ← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

set_option backward.privateInPublic true in
/-- A preparatory function for making a 2-cocycle from a linear splitting of an extension. -/
/-
**LieAlgebra.Extension.twoCocycleAux** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra.Ext
ension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preparatory function for making a 2-cocycle from a linear splitting of an exte
nsion.
-/
private abbrev twoCocycleAux (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) :
    L →ₗ[R] L →ₗ[R] E.proj.ker where
  toFun x :=
    { toFun y := ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_sub] }
  map_add' x y := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The 2-cocycle attached to an extension with a linear section. -/
@[simps]
/-
**LieAlgebra.Extension.twoCocycleOf** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extens
ion`。
形式化陈述：twoCocycleOf [IsLieAbelian M] (E : Extension R M L) {s : L ->ₗ[R] E.L} (hs
 : LeftInverse E.proj s) : letI
参数：E : Extension R M L；hs : LeftInverse E.proj s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieAlgebra.Extension.lieModuleOf`：lieModuleOf [IsLieAbelian M] (E : Exte
nsion R M L) : letI

--- 原说明 ---
The 2-cocycle attached to an extension with a linear section.
-/
noncomputable def twoCocycleOf [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) :
    letI := E.ringModuleOf
    have := E.lieModuleOf
    twoCocycle R L M where
  val := ⟨(E.twoCocycleAux hs).compr₂ E.toKer.symm, by simp⟩
  property := by
    -- TODO Try to golf this after https://github.com/leanprover-community/mathlib4/pull/27306 lands
    ext x y z
    suffices ⁅s x, ⁅s y, s z⁆⁆ - ⁅s x, s ⁅y, z⁆⁆ -
        (⁅s y, ⁅s x, s z⁆⁆ - ⁅s y, s ⁅x, z⁆⁆) + (⁅s z, ⁅s x, s y⁆⁆ - ⁅s z, s ⁅x, y⁆⁆) -
          (⁅s ⁅x, y⁆, s z⁆ - (s ⁅x, ⁅y, z⁆⁆ - s ⁅y, ⁅x, z⁆⁆)) +
        (⁅s ⁅x, z⁆, s y⁆ - (s ⁅x, ⁅z, y⁆⁆ - s ⁅z, ⁅x, y⁆⁆)) -
        (⁅s ⁅y, z⁆, s x⁆ - (s ⁅y, ⁅z, x⁆⁆ - s ⁅z, ⁅y, x⁆⁆)) = 0 by
      set h := E.proj_surjective.hasRightInverse
      have aux (u : L) (v : E.proj.ker) : ⁅h.choose u, v⁆ = ⁅s u, v⁆ := by
        rw [← E.lie_apply_proj_of_leftInverse_eq hs, h.choose_spec _]
      simpa [← map_sub, ← map_add, ← twoCochain_val_apply, Subtype.ext_iff, twoCocycleAux, aux]
    have hjac := lie_lie (s x) (s y) (s z)
    rw [← lie_skew, neg_eq_iff_eq_neg] at hjac
    have hja := congr_arg s (lie_lie x y z)
    rw [← lie_skew, map_neg, neg_eq_iff_eq_neg] at hja
    have hj := congr_arg s (lie_lie y x z)
    rw [← lie_skew, map_neg, neg_eq_iff_eq_neg] at hj
    rw [hjac, hj, hja, ← lie_skew y z, ← lie_skew _ (s (-⁅z, y⁆)), ← lie_skew (s ⁅x, z⁆),
      ← lie_skew (s ⁅x, y⁆), ← lie_skew x z]
    simp only [map_neg, neg_lie, neg_neg, neg_sub, lie_neg, sub_neg_eq_add,
      sub_add_cancel_right, map_add, neg_add_rev]
    abel_nf

/-- The 1-cochain attached to a pair of splittings of an extension. -/
@[simps]
/-
**LieAlgebra.Extension.oneCochainOfTwoSplitting** 是 Mathlib 中的一个定义，位于命名空间 `LieAl
gebra.Extension`。
形式化陈述：oneCochainOfTwoSplitting (E : Extension R M L) {s₁ s₂ : L ->ₗ[R] E.L} (hs₁
 : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) : oneCochain R L M where
 toFun x
参数：E : Extension R M L；hs₁ : LeftInverse E.proj s₁；hs₂ : LeftInverse E.proj s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-cochain attached to a pair of splittings of an extension.
-/
noncomputable def oneCochainOfTwoSplitting (E : Extension R M L) {s₁ s₂ : L →ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) :
    oneCochain R L M where
  toFun x :=
    E.toKer.symm ⟨(s₁ x) - (s₂ x), LieHom.mem_ker.mpr (by rw [map_sub, sub_eq_zero, hs₁, hs₂])⟩
  map_add' _ _ := by
    rw [← map_add, AddMemClass.mk_add_mk, EquivLike.apply_eq_iff_eq, Subtype.mk_eq_mk, map_add,
      map_add, add_sub_add_comm]
  map_smul' _ _ := by
    rw [RingHom.id_apply, ← map_smul, EquivLike.apply_eq_iff_eq, SetLike.mk_smul_of_tower_mk,
      Subtype.mk_eq_mk, LinearMap.map_smul_of_tower, smul_sub, LinearMap.map_smul_of_tower]
/-
**LieAlgebra.Extension.d** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁₂_oneCochainOfTwoSplitting [IsLieAbelian M] (E : Extension R M L) {s₁ s₂ : L →ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    d₁₂ R L M (E.oneCochainOfTwoSplitting hs₁ hs₂) = E.twoCocycleOf hs₁ - E.twoCocycleOf hs₂ := by
  ext x y
  choose s hs using E.proj_surjective
  have {s' : L → E.L} (h : LeftInverse E.proj s') : ⁅s x - s' x, s' y - s y⁆ = (0 : E.L) := by
    have aux := trivial_lie_zero E.proj.ker E.proj.ker
      ⟨s x - s' x, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
      ⟨s' y - s y, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
    simpa only [Subtype.ext_iff, LieSubmodule.coe_zero, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket] using aux
  replace this {s' : L → E.L} (h : LeftInverse E.proj s') :
      ⁅s x, s' y⁆ = ⁅s' x, s' y⁆ + (⁅s x, s y⁆ - ⁅s' x, s y⁆) := by
    simpa [sub_sub, sub_eq_zero] using this h
  simp only [d₁₂_apply_coe_apply_apply, oneCochainOfTwoSplitting_apply, AddSubgroupClass.coe_sub,
    twoCocycleOf_coe_coe, LinearMap.sub_apply, LinearMap.compr₂_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  nth_rw 1 [← hs x]
  nth_rw 4 [← hs y]
  simp only [← EmbeddingLike.apply_eq_iff_eq E.toKer, ringModuleOf_bracket_proj,
    LieEquiv.apply_symm_apply, map_sub, Subtype.ext_iff, AddSubgroupClass.coe_sub,
    LieSubmodule.coe_bracket, lie_sub, this hs₁, this hs₂, ← lie_skew (s₁ x) (s y),
    ← lie_skew (s₂ x) (s y)]
  abel

end LieAlgebra.Extension

