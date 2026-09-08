/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Moritz Doll
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Prod

/-!
# Partially defined linear maps

A `LinearPMap σ E F` or `E →ₛₗ.[σ] F` is a semilinear map from a submodule of `E` to `F` with a ring
homomorphism `σ` between the scalars. This reduces to a linear map when `σ` is the identity.
We define a `SemilatticeInf` with `OrderBot` instance on this, and define three operations:

* `mkSpanSingleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `sSup` takes a `DirectedOn (· ≤ ·)` set of partial linear maps, and returns the unique
  partial linear map on the `sSup` of their domains that extends all these maps.

Moreover, we define
* `LinearPMap.graph` is the graph of the partial linear map viewed as a submodule of `E × F`.
TODO: This should be also generalized to semilinear maps, but one has to define a new type where `R`
acts on `E` normally while `R` acts on `F` through `σ`.

Partially defined maps are currently used in `Mathlib` to prove the Hahn-Banach theorem
and its variations. Namely, `LinearPMap.sSup` implies that every chain of `LinearPMap`s
is bounded above.
They are also the basis for the theory of unbounded operators.

-/

@[expose] public section

/-- A `LinearPMap σ E F` or `E →ₛₗ.[σ] F` is a (semi)linear map from a submodule of `E` to `F`. -/
/-
**LinearPMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Ring R] →       [inst_1 : 
Ring S] →         (R →+* S) →           (E : Type u_3) →             [inst_2 : A
ddCommGroup E] →               [_root_.Module R E] → (F : Type u_4) → [inst : Ad
dCommGroup F] → [_root_.Module S F] → Type (max u_3 u_4)
参数：R →+* S；E : Type u_3；F : Type u_4；max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LinearPMap σ E F` or `E →ₛₗ.[σ] F` is a (semi)linear map from a submodule of 
`E` to `F`.
-/
structure LinearPMap {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) (E : Type*)
    [AddCommGroup E] [Module R E] (F : Type*) [AddCommGroup F] [Module S F] where
  /-- The domain of the (semi)linear map. -/
  domain : Submodule R E
  /-- The (semi)linear map itself. -/
  toFun : domain →ₛₗ[σ] F

@[inherit_doc] notation:25 E " →ₛₗ.[" σ:25 "] " F:0 => LinearPMap σ E F

/-- `E →ₗ.[R] F` is the notation for `E →ₛₗ.[RingHom.id R] F`. -/
notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPMap (RingHom.id R) E F

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : S →+* T} {E : Type*}
  [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F] {G : Type*}
  [AddCommGroup G] [Module T G]

namespace LinearPMap

open Submodule

/-- The (semi)linear map as just a function. -/
@[coe]
/-
**LinearPMap.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：toFun' (f : E ->ₛₗ.[σ] F) : f.domain -> F
参数：f : E ->ₛₗ.[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (semi)linear map as just a function.
-/
def toFun' (f : E →ₛₗ.[σ] F) : f.domain → F := f.toFun
/-
**LinearPMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (E →ₛₗ.[σ] F) fun f : E →ₛₗ.[σ] F => f.domain → F :=
  ⟨toFun'⟩

@[simp]
/-
**LinearPMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：toFun_eq_coe (f : E ->ₛₗ.[σ] F) (x : f.domain) : f.toFun x = f x
参数：f : E ->ₛₗ.[σ] F；x : f.domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : E →ₛₗ.[σ] F) (x : f.domain) : f.toFun x = f x :=
  rfl

@[ext (iff := false)]
/-
**LinearPMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' : forall ⦃x : E⦄ ⦃h
f : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g
参数：h : f.domain = g.domain；h' : forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g
.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem ext {f g : E →ₛₗ.[σ] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g := by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  congr
  apply LinearMap.ext
  intro x
  apply h'

/-- A dependent version of `ext`. -/
/-
**LinearPMap.dExt** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：dExt {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' : forall ⦃x : f.do
main⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g
参数：h : f.domain = g.domain；h' : forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : 
E) = y), f x = g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.ext`：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' :
 forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
) : …

--- 原说明 ---
A dependent version of `ext`.
-/
theorem dExt {f g : E →ₛₗ.[σ] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g :=
  ext h fun _ _ _ ↦ h' rfl

@[simp]
/-
**LinearPMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
参数：f : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem map_zero (f : E →ₛₗ.[σ] F) : f 0 = 0 :=
  f.toFun.map_zero
/-
**LinearPMap.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：ext_iff {f g : E ->ₛₗ.[σ] F} : f = g ↔ f.domain = g.domain ∧ forall ⦃x : E
⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LinearPMap.ext`：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' :
 forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
) : …
-/
theorem ext_iff {f g : E →ₛₗ.[σ] F} :
    f = g ↔
      f.domain = g.domain ∧
        ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩ :=
  ⟨by rintro rfl; simp, fun ⟨deq, feq⟩ ↦ ext deq feq⟩
/-
**LinearPMap.dExt_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：dExt_iff {f g : E ->ₛₗ.[σ] F} : f = g ↔ exists _domain_eq : f.domain = g.d
omain, forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.dExt`：dExt {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h'
 : forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g
-/
theorem dExt_iff {f g : E →ₛₗ.[σ] F} :
    f = g ↔
      ∃ _domain_eq : f.domain = g.domain,
        ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y :=
  ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => dExt deq feq⟩
/-
**LinearPMap.ext'** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：ext' {s : Submodule R E} {f g : s ->ₛₗ[σ] F} (h : f = g) : mk s f = mk s g
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext' {s : Submodule R E} {f g : s →ₛₗ[σ] F} (h : f = g) : mk s f = mk s g :=
  h ▸ rfl
/-
**LinearPMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_add (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x + y) = f x + f y
参数：f : E ->ₛₗ.[σ] F；x y : f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem map_add (f : E →ₛₗ.[σ] F) (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y
/-
**LinearPMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_neg (f : E ->ₛₗ.[σ] F) (x : f.domain) : f (-x) = -f x
参数：f : E ->ₛₗ.[σ] F；x : f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem map_neg (f : E →ₛₗ.[σ] F) (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x
/-
**LinearPMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x - y) = f x - f y
参数：f : E ->ₛₗ.[σ] F；x y : f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem map_sub (f : E →ₛₗ.[σ] F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y
/-
**LinearPMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_smul [Module R F] (f : E ->ₗ.[R] F) (c : R) (x : f.domain) : f (c • x)
 = c • f x
参数：f : E ->ₗ.[R] F；c : R；x : f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
-/
theorem map_smul [Module R F] (f : E →ₗ.[R] F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.toFun.map_smulₛₗ c x
/-
**LinearPMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：map_smul [Module R F] (f : E ->ₗ.[R] F) (c : R) (x : f.domain) : f (c • x)
 = c • f x
参数：f : E ->ₗ.[R] F；c : R；x : f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
-/
theorem map_smulₛₗ (f : E →ₛₗ.[σ] F) (c : R) (x : f.domain) : f (c • x) = σ c • f x :=
  f.toFun.map_smulₛₗ c x

@[simp]
/-
**LinearPMap.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mk_apply (p : Submodule R E) (f : p ->ₛₗ[σ] F) (x : p) : mk p f x = f x
参数：p : Submodule R E；f : p ->ₛₗ[σ] F；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply (p : Submodule R E) (f : p →ₛₗ[σ] F) (x : p) : mk p f x = f x := rfl

/-- The unique `LinearPMap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
/-
**LinearPMap.mkSpanSingleton'** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：mkSpanSingleton' (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y =
 0) : E ->ₛₗ.[σ] F where domain
参数：x : E；y : F；H : forall c : R, c • x = 0 -> σ c • y = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique `LinearPMap` on `R ∙ x` that sends `x` to `y`. This version works for
 modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`.
-/
noncomputable def mkSpanSingleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → σ c • y = 0) :
    E →ₛₗ.[σ] F where
  domain := R ∙ x
  toFun :=
    have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → σ c₁ • y = σ c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero, ← sub_smul] at h ⊢
      rw [← RingHom.map_sub]
      exact H _ h
    { toFun z := σ (Classical.choose (mem_span_singleton.1 z.prop)) • y
      map_add' y' z' := by
        rw [← add_smul, ← RingHom.map_add, H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [add_smul, this, ← coe_add]
      map_smul' c z := by
        rw [smul_smul, ← RingHom.map_mul, H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [mul_smul, this]
        apply coe_smul }

@[simp]
/-
**LinearPMap.domain_mkSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domain_mkSpanSingleton (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c
 • y = 0) : (mkSpanSingleton' x y H).domain = R ∙ x
参数：x : E；y : F；H : forall c : R, c • x = 0 -> σ c • y = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domain_mkSpanSingleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → σ c • y = 0) :
    (mkSpanSingleton' x y H).domain = R ∙ x :=
  rfl

@[simp]
/-
**LinearPMap.mkSpanSingleton'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F] (x : E) (y :
 F)   (H : ∀ (c : R), c • x = 0 → σ c • y = 0) (c : R) (h : c • x ∈ (LinearPMap.
mkSpanSingleton' x y H).domain),   ↑(LinearPMap.mkSpanSingleton' x y H) ⟨c • x, 
h⟩ = σ c • y
参数：x : E；y : F；H : ∀ (c : R), c • x = 0 → σ c • y = 0；c : R；h : c • x ∈ (LinearP
Map.mkSpanSingleton' x y H).domain；LinearPMap.mkSpanSingleton' x y H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
-/
theorem mkSpanSingleton'_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → σ c • y = 0) (c : R) (h) :
    mkSpanSingleton' x y H ⟨c • x, h⟩ = σ c • y := by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero, ← sub_smul, ← RingHom.map_sub]
  apply H
  simp only [sub_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)

@[simp]
/-
**LinearPMap.mkSpanSingleton'_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F] (x : E) (y :
 F)   (H : ∀ (c : R), c • x = 0 → σ c • y = 0) (h : x ∈ (LinearPMap.mkSpanSingle
ton' x y H).domain),   ↑(LinearPMap.mkSpanSingleton' x y H) ⟨x, h⟩ = y
参数：x : E；y : F；H : ∀ (c : R), c • x = 0 → σ c • y = 0；h : x ∈ (LinearPMap.mkSpan
Singleton' x y H).domain；LinearPMap.mkSpanSingleton' x y H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `LinearPMap.mkSpanSingleton'_apply`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup
 E]   [inst_3 : _root_.…
-/
theorem mkSpanSingleton'_apply_self (x : E) (y : F) (H : ∀ c : R, c • x = 0 → σ c • y = 0) (h) :
    mkSpanSingleton' x y H ⟨x, h⟩ = y := by
  conv_rhs => rw [← one_smul S y]
  rw [← RingHom.map_one, ← mkSpanSingleton'_apply x y H 1 ?_]
  · congr
    rw [one_smul]
  · rwa [one_smul]

/-- The unique `LinearPMap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
/-
**LinearPMap.mkSpanSingleton** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearPMap`。
形式化陈述：mkSpanSingleton {K L E F : Type*} [DivisionRing K] [DivisionRing L] {σ : K
 ->+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module L F] (x : E) (y 
: F) (hx : x != 0) : E ->ₛₗ.[σ] F
参数：x : E；y : F；hx : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique `LinearPMap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings.
-/
noncomputable abbrev mkSpanSingleton {K L E F : Type*} [DivisionRing K] [DivisionRing L]
    {σ : K →+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module L F] (x : E) (y : F)
    (hx : x ≠ 0) : E →ₛₗ.[σ] F :=
  mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, RingHom.map_zero, zero_smul]) fun hx' =>
    absurd hx' hx
/-
**LinearPMap.mkSpanSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mkSpanSingleton_apply (K L : Type*) {E F : Type*} [DivisionRing K] [Divisi
onRing L] {σ : K ->+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module 
L F] {x : E} (hx : x != 0) (y : F) : (mkSpanSingleton x y hx : E ->ₛₗ.[σ] F) ⟨x,
 (Submodule.mem_span_singleton_self x : x in Submodule.span K {x})⟩ = y
参数：K L : Type*；hx : x != 0；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.mkSpanSingleton'_apply_self`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddComm
Group E]   [inst_3 : _root_.…
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
-/
theorem mkSpanSingleton_apply (K L : Type*) {E F : Type*} [DivisionRing K] [DivisionRing L]
    {σ : K →+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module L F] {x : E} (hx : x ≠ 0)
    (y : F) :
    (mkSpanSingleton x y hx : E →ₛₗ.[σ] F)
      ⟨x, (Submodule.mem_span_singleton_self x : x ∈ Submodule.span K {x})⟩ = y :=
  LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- Projection to the first coordinate as a `LinearPMap` -/
/-
**LinearPMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {E : Type u_4} →       [inst_1 : 
AddCommGroup E] →         [inst_2 : _root_.Module R E] →           {F : Type u_5
} →             [inst_3 : AddCommGroup F] → [inst_4 : _root_.Module R F] → Submo
dule R E → Submodule R F → E × F →ₗ.[R] E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to the first coordinate as a `LinearPMap`
-/
protected def fst [Module R F] (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] E where
  domain := p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype

@[simp]
/-
**LinearPMap.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：fst_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.pro
d p') : LinearPMap.fst p p' x = (x : E × F).1
参数：p : Submodule R E；p' : Submodule R F；x : p.prod p'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.fst p p' x = (x : E × F).1 :=
  rfl

/-- Projection to the second coordinate as a `LinearPMap` -/
/-
**LinearPMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {E : Type u_4} →       [inst_1 : 
AddCommGroup E] →         [inst_2 : _root_.Module R E] →           {F : Type u_5
} →             [inst_3 : AddCommGroup F] → [inst_4 : _root_.Module R F] → Submo
dule R E → Submodule R F → E × F →ₗ.[R] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to the second coordinate as a `LinearPMap`
-/
protected def snd [Module R F] (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] F where
  domain := p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype

@[simp]
/-
**LinearPMap.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：snd_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.pro
d p') : LinearPMap.snd p p' x = (x : E × F).2
参数：p : Submodule R E；p' : Submodule R F；x : p.prod p'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.snd p p' x = (x : E × F).2 :=
  rfl
/-
**LinearPMap.le** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：le : LE (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance le : LE (E →ₛₗ.[σ] F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩
/-
**LinearPMap.apply_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：apply_comp_inclusion {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain) : T 
x = S (Submodule.inclusion h.1 x)
参数：h : T <= S；x : T.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem apply_comp_inclusion {T S : E →ₛₗ.[σ] F} (h : T ≤ S) (x : T.domain) :
    T x = S (Submodule.inclusion h.1 x) :=
  h.2 rfl
/-
**LinearPMap.exists_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：exists_of_le {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain) : exists y :
 S.domain, (x : E) = y ∧ T x = S y
参数：h : T <= S；x : T.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_of_le {T S : E →ₛₗ.[σ] F} (h : T ≤ S) (x : T.domain) :
    ∃ y : S.domain, (x : E) = y ∧ T x = S y :=
  ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩
/-
**LinearPMap.eq_of_le_of_domain_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：eq_of_le_of_domain_eq {f g : E ->ₛₗ.[σ] F} (hle : f <= g) (heq : f.domain 
= g.domain) : f = g
参数：hle : f <= g；heq : f.domain = g.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.dExt`：dExt {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h'
 : forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_of_le_of_domain_eq {f g : E →ₛₗ.[σ] F} (hle : f ≤ g) (heq : f.domain = g.domain) :
    f = g :=
  dExt heq hle.2

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
/-
**LinearPMap.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：eqLocus (f g : E ->ₛₗ.[σ] F) : Submodule R E where carrier
参数：f g : E ->ₛₗ.[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule.
-/
def eqLocus (f g : E →ₛₗ.[σ] F) : Submodule R E where
  carrier := { x | ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' {x y} := fun ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ ↦
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      simp_all [← AddMemClass.mk_add_mk, f.map_add, g.map_add]⟩
  smul_mem' c x := fun ⟨hfx, hgx, hx⟩ ↦
    ⟨smul_mem _ c hfx, smul_mem _ c hgx, by
      have {f : E →ₛₗ.[σ] F} (hfx) : (⟨c • x, smul_mem _ c hfx⟩ : f.domain) = c • ⟨x, hfx⟩ := by
        simp
      rw [this hfx, this hgx, f.map_smulₛₗ, g.map_smulₛₗ, hx]⟩
/-
**LinearPMap.bot** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：bot : Bot (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bot : Bot (E →ₛₗ.[σ] F) :=
  ⟨⟨⊥, 0⟩⟩
/-
**LinearPMap.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：inhabited : Inhabited (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (E →ₛₗ.[σ] F) :=
  ⟨⊥⟩
/-
**LinearPMap.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：semilatticeInf : SemilatticeInf (E ->ₛₗ.[σ] F) where le_refl f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf : SemilatticeInf (E →ₛₗ.[σ] F) where
  le_refl f := ⟨le_refl f.domain, fun _ _ h => Subtype.ext h ▸ rfl⟩
  le_trans := fun _ _ _ ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x _ hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm _ _ fg gf := eq_of_le_of_domain_eq fg (le_antisymm fg.1 gf.1)
  inf f g := ⟨f.eqLocus g, f.toFun.comp <| inclusion fun _x hx => hx.fst⟩
  le_inf := by
    intro f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩
    exact ⟨fun x hx =>
      ⟨fg_le hx, fh_le hx,
      (fg_eq (x := ⟨x, hx⟩) rfl).symm.trans (fh_eq rfl)⟩,
      fun x ⟨y, yg, hy⟩ h => fg_eq h⟩
  inf_le_left f _ := ⟨fun _ hx => hx.fst, fun _ _ h => congr_arg f <| Subtype.ext <| h⟩
  inf_le_right _ g :=
    ⟨fun _ hx => hx.snd.fst, fun ⟨_, _, _, hx⟩ _ h => hx.trans <| congr_arg g <| Subtype.ext <| h⟩
/-
**LinearPMap.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：orderBot : OrderBot (E ->ₛₗ.[σ] F) where bot_le f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot : OrderBot (E →ₛₗ.[σ] F) where
  bot_le f :=
    ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.ext ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.ext (h.symm.trans (congr_arg _ hx))
      rw [hx, hy, map_zero, map_zero]⟩
/-
**LinearPMap.le_of_eqLocus_ge** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：le_of_eqLocus_ge {f g : E ->ₛₗ.[σ] F} (H : f.domain <= f.eqLocus g) : f <=
 g
参数：H : f.domain <= f.eqLocus g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem le_of_eqLocus_ge {f g : E →ₛₗ.[σ] F} (H : f.domain ≤ f.eqLocus g) : f ≤ g :=
  suffices f ≤ f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g ≤ f).2 hxy.symm).symm⟩
/-
**LinearPMap.domain_mono** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domain_mono : StrictMono (domain (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LinearPMap.eq_of_le_of_domain_eq`：eq_of_le_of_domain_eq {f g : E ->ₛₗ.[σ
] F} (hle : f <= g) (heq : f.domain = g.domain) : f = g
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem domain_mono : StrictMono (domain (σ := σ) (E := E) (F := F)) :=
  fun _f _g hlt =>
    lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt <| eq_of_le_of_domain_eq (le_of_lt hlt) heq

set_option backward.privateInPublic true in
/-
**LinearPMap.sup_aux** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sup_aux (f g : E →ₛₗ.[σ] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    ∃ fg : ↥(f.domain ⊔ g.domain) →ₛₗ[σ] F,
      ∀ (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)),
        (x : E) + y = ↑z → fg z = f x + g y := by
  choose x hx y hy hxy using fun z : ↥(f.domain ⊔ g.domain) => mem_sup.1 z.prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq : ∀ (x' : f.domain) (y' : g.domain) (z' : ↥(f.domain ⊔ g.domain))
      (_H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
    dsimp [fg]
    rw [add_comm, ← sub_eq_sub_iff_add_eq_add, eq_comm, ← map_sub, ← map_sub]
    apply h
    simp only [← eq_sub_iff_add_eq] at hxy
    simp only [AddSubgroupClass.coe_sub, hxy, ← sub_add, ← sub_sub, sub_self,
      zero_sub, ← H]
    apply neg_add_eq_sub
  use { toFun := fg, map_add' := ?_, map_smul' := ?_ }, fg_eq
  · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    rw [← add_assoc, add_right_comm (f _), ← map_add, add_assoc, ← map_add]
    apply fg_eq
    simp only [coe_add, ← add_assoc]
    rw [add_right_comm (x _), hxy, add_assoc, hxy, coe_mk, coe_mk]
  · intro c z
    rw [smul_add, ← map_smulₛₗ, ← map_smulₛₗ]
    apply fg_eq
    simp only [coe_smul, ← smul_add, hxy]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
/-
**LinearPMap.sup** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Ring R] →       [inst_1 : 
Ring S] →         {σ : R →+* S} →           {E : Type u_4} →             [inst_2
 : AddCommGroup E] →               [inst_3 : _root_.Module R E] →               
  {F : Type u_5} →                   [inst_4 : AddCommGroup F] →                
     [inst_5 : _root_.Module S F] →                       (f g : E →ₛₗ.[σ] F) → 
(∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y) → E →ₛₗ.[σ] F
参数：f g : E →ₛₗ.[σ] F；∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearPMap.0.LinearPMap.sup_aux`：∀ {R : T
ype u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Typ
e u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.…

--- 原说明 ---
Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agree
s
with `f` and `g`.
-/
protected noncomputable def sup (f g : E →ₛₗ.[σ] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : E →ₛₗ.[σ] F :=
  ⟨_, Classical.choose (sup_aux f g h)⟩

@[simp]
/-
**LinearPMap.domain_sup** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domain_sup (f g : E ->ₛₗ.[σ] F) (h : forall (x : f.domain) (y : g.domain),
 (x : E) = y -> f x = g y) : (f.sup g h).domain = f.domain ⊔ g.domain
参数：f g : E ->ₛₗ.[σ] F；h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f
 x = g y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domain_sup (f g : E →ₛₗ.[σ] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    (f.sup g h).domain = f.domain ⊔ g.domain :=
  rfl
/-
**LinearPMap.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：sup_apply {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.domain) (y : g.domain), 
(x : E) = y -> f x = g y) (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.doma
in)) (hz : (↑x : E) + ↑y = ↑z) : f.sup g H z = f x + g y
参数：H : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y；x : f.doma
in；y : g.domain；z : ↥(f.domain ⊔ g.domain)；hz : (↑x : E) + ↑y = ↑z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearPMap.0.LinearPMap.sup_aux`：∀ {R : T
ype u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Typ
e u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.…
-/
theorem sup_apply {f g : E →ₛₗ.[σ] F} (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y)
    (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)) (hz : (↑x : E) + ↑y = ↑z) :
    f.sup g H z = f x + g y :=
  Classical.choose_spec (sup_aux f g H) x y z hz
/-
**LinearPMap.left_le_sup** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F] (f g : E →ₛₗ
.[σ] F)   (h : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y), f ≤ f.
sup g h
参数：f g : E →ₛₗ.[σ] F；h : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g 
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `LinearPMap.sup_apply`：sup_apply {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.
domain) (y : g.domain), (x : E) = y -> f x = g y) (x : f.domain) (y : g.domain) 
(z : ↥(f.d…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
protected theorem left_le_sup (f g : E →ₛₗ.[σ] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : f ≤ f.sup g h := by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _), ← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
/-
**LinearPMap.right_le_sup** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F] (f g : E →ₛₗ
.[σ] F)   (h : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y), g ≤ f.
sup g h
参数：f g : E →ₛₗ.[σ] F；h : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g 
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `LinearPMap.sup_apply`：sup_apply {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.
domain) (y : g.domain), (x : E) = y -> f x = g y) (x : f.domain) (y : g.domain) 
(z : ↥(f.d…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
protected theorem right_le_sup (f g : E →ₛₗ.[σ] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : g ≤ f.sup g h := by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _), ← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
/-
**LinearPMap.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F]   {f g h : E
 →ₛₗ.[σ] F} (H : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y), f ≤ 
h → g ≤ h → f.sup g H ≤ h
参数：H : ∀ (x : ↥f.domain) (y : ↥g.domain), ↑x = ↑y → ↑f x = ↑g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `LinearPMap.left_le_sup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] 
[inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst
_3 : _root_.…
· 使用定理 `LinearPMap.right_le_sup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R]
 [inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [ins
t_3 : _root_.…
· 使用定理 `LinearPMap.le_of_eqLocus_ge`：le_of_eqLocus_ge {f g : E ->ₛₗ.[σ] F} (H : 
f.domain <= f.eqLocus g) : f <= g
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem sup_le {f g h : E →ₛₗ.[σ] F}
    (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) (fh : f ≤ h) (gh : g ≤ h) :
    f.sup g H ≤ h :=
  have Hf : f ≤ f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g ≤ f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
  le_of_eqLocus_ge <| sup_le Hf.1 Hg.1

/-- Hypothesis for `LinearPMap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
/-
**LinearPMap.sup_h_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：sup_h_of_disjoint (f g : E ->ₛₗ.[σ] F) (h : Disjoint f.domain g.domain) (x
 : f.domain) (y : g.domain) (hxy : (x : E) = y) : f x = g y
参数：f g : E ->ₛₗ.[σ] F；h : Disjoint f.domain g.domain；x : f.domain；y : g.domain；h
xy : (x : E) = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Hypothesis for `LinearPMap.sup` holds, if `f.domain` is disjoint with `g.domain`
.
-/
theorem sup_h_of_disjoint (f g : E →ₛₗ.[σ] F) (h : Disjoint f.domain g.domain) (x : f.domain)
    (y : g.domain) (hxy : (x : E) = y) : f x = g y := by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.ext (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.ext (hxy.trans <| congr_arg _ hy)
  simp [*]

/-! ### Algebraic operations -/


section Zero

/-
**LinearPMap.instZero** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instZero : Zero (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (E →ₛₗ.[σ] F) := ⟨⊤, 0⟩

@[simp]
/-
**LinearPMap.zero_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：zero_domain : (0 : E ->ₛₗ.[σ] F).domain = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_domain : (0 : E →ₛₗ.[σ] F).domain = ⊤ := rfl

@[simp]
/-
**LinearPMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：zero_apply (x : (⊤ : Submodule R E)) : (0 : E ->ₛₗ.[σ] F) x = 0
参数：x : (⊤ : Submodule R E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : (⊤ : Submodule R E)) : (0 : E →ₛₗ.[σ] F) x = 0 := rfl

end Zero

section SMul

variable {M N : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass S M F]
variable [Monoid N] [DistribMulAction N F] [SMulCommClass S N F]

/-
**LinearPMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instSMul : SMul M (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul M (E →ₛₗ.[σ] F) :=
  ⟨fun a f =>
    { domain := f.domain
      toFun := a • f.toFun }⟩

@[simp]
/-
**LinearPMap.smul_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：smul_domain (a : M) (f : E ->ₛₗ.[σ] F) : (a • f).domain = f.domain
参数：a : M；f : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_domain (a : M) (f : E →ₛₗ.[σ] F) : (a • f).domain = f.domain :=
  rfl
/-
**LinearPMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：smul_apply (a : M) (f : E ->ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a
 • f x
参数：a : M；f : E ->ₛₗ.[σ] F；x : (a • f).domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (a : M) (f : E →ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a • f x :=
  rfl

@[simp]
/-
**LinearPMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：coe_smul (a : M) (f : E ->ₛₗ.[σ] F) : ⇑(a • f) = a • ⇑f
参数：a : M；f : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (a : M) (f : E →ₛₗ.[σ] F) : ⇑(a • f) = a • ⇑f :=
  rfl
/-
**LinearPMap.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instSMulCommClass [SMulCommClass M N F] : SMulCommClass M N (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.ext'`：ext' {s : Submodule R E} {f g : s ->ₛₗ[σ] F} (h : f = g
) : mk s f = mk s g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
instance instSMulCommClass [SMulCommClass M N F] : SMulCommClass M N (E →ₛₗ.[σ] F) :=
  ⟨fun a b f => ext' <| smul_comm a b f.toFun⟩
/-
**LinearPMap.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instIsScalarTower [SMul M N] [IsScalarTower M N F] : IsScalarTower M N (E 
->ₛₗ.[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.ext'`：ext' {s : Submodule R E} {f g : s ->ₛₗ[σ] F} (h : f = g
) : mk s f = mk s g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
instance instIsScalarTower [SMul M N] [IsScalarTower M N F] : IsScalarTower M N (E →ₛₗ.[σ] F) :=
  ⟨fun a b f => ext' <| smul_assoc a b f.toFun⟩
/-
**LinearPMap.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instMulAction : MulAction M (E ->ₛₗ.[σ] F) where one_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction : MulAction M (E →ₛₗ.[σ] F) where
  one_smul := fun ⟨_s, f⟩ => ext' <| one_smul M f
  mul_smul a b f := ext' <| mul_smul a b f.toFun

end SMul

/-
**LinearPMap.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instNeg : Neg (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (E →ₛₗ.[σ] F) :=
  ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]
/-
**LinearPMap.neg_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：neg_domain (f : E ->ₛₗ.[σ] F) : (-f).domain = f.domain
参数：f : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_domain (f : E →ₛₗ.[σ] F) : (-f).domain = f.domain := rfl

@[simp]
/-
**LinearPMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：neg_apply (f : E ->ₛₗ.[σ] F) (x) : (-f) x = -f x
参数：f : E ->ₛₗ.[σ] F；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : E →ₛₗ.[σ] F) (x) : (-f) x = -f x :=
  rfl
/-
**LinearPMap.instInvolutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instInvolutiveNeg : InvolutiveNeg (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveNeg : InvolutiveNeg (E →ₛₗ.[σ] F) :=
  ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]⟩

section Add

/-
**LinearPMap.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAdd : Add (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (E →ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain ≤ _))
        + g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain ≤ _)) }⟩
/-
**LinearPMap.add_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：add_domain (f g : E ->ₛₗ.[σ] F) : (f + g).domain = f.domain ⊓ g.domain
参数：f g : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_domain (f g : E →ₛₗ.[σ] F) : (f + g).domain = f.domain ⊓ g.domain := rfl
/-
**LinearPMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：add_apply (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E))
 : (f + g) x = f ⟨x, x.prop.1⟩ + g ⟨x, x.prop.2⟩
参数：f g : E ->ₛₗ.[σ] F；x : (f.domain ⊓ g.domain : Submodule R E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f + g) x = f ⟨x, x.prop.1⟩ + g ⟨x, x.prop.2⟩ := rfl
/-
**LinearPMap.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAddSemigroup : AddSemigroup (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddSemigroup : AddSemigroup (E →ₛₗ.[σ] F) :=
  ⟨fun f g h => by
    ext x y hxy
    · simp only [add_domain, inf_assoc]
    · simp only [add_apply, add_assoc]⟩
/-
**LinearPMap.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAddZeroClass : AddZeroClass (E ->ₛₗ.[σ] F) where zero_add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass : AddZeroClass (E →ₛₗ.[σ] F) where
  zero_add := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
  add_zero := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
/-
**LinearPMap.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAddMonoid : AddMonoid (E ->ₛₗ.[σ] F) where zero_add f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid : AddMonoid (E →ₛₗ.[σ] F) where
  zero_add f := by
    simp
  add_zero := by
    simp
  nsmul := nsmulRec
/-
**LinearPMap.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAddCommMonoid : AddCommMonoid (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (E →ₛₗ.[σ] F) :=
  ⟨fun f g => by
    ext x y hxy
    · simp only [add_domain, inf_comm]
    · simp only [add_apply, add_comm]⟩

end Add

section VAdd

/-
**LinearPMap.instVAdd** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instVAdd : VAdd (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instVAdd : VAdd (E →ₛₗ[σ] F) (E →ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩

@[simp]
/-
**LinearPMap.vadd_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：vadd_domain (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) : (f +ᵥ g).domain = g.dom
ain
参数：f : E ->ₛₗ[σ] F；g : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_domain (f : E →ₛₗ[σ] F) (g : E →ₛₗ.[σ] F) : (f +ᵥ g).domain = g.domain :=
  rfl
/-
**LinearPMap.vadd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：vadd_apply (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) (x : (f +ᵥ g).domain) : (f
 +ᵥ g) x = f x + g x
参数：f : E ->ₛₗ[σ] F；g : E ->ₛₗ.[σ] F；x : (f +ᵥ g).domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_apply (f : E →ₛₗ[σ] F) (g : E →ₛₗ.[σ] F) (x : (f +ᵥ g).domain) :
    (f +ᵥ g) x = f x + g x :=
  rfl

@[simp]
/-
**LinearPMap.coe_vadd** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：coe_vadd (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) : ⇑(f +ᵥ g) = ⇑(f.comp g.dom
ain.subtype) + ⇑g
参数：f : E ->ₛₗ[σ] F；g : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vadd (f : E →ₛₗ[σ] F) (g : E →ₛₗ.[σ] F) : ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g :=
  rfl
/-
**LinearPMap.instAddAction** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instAddAction : AddAction (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F) where vadd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddAction : AddAction (E →ₛₗ[σ] F) (E →ₛₗ.[σ] F) where
  vadd := (· +ᵥ ·)
  zero_vadd := fun ⟨_s, _f⟩ => ext' <| zero_add _
  add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' <| LinearMap.ext fun _x => add_assoc _ _ _

end VAdd

section Sub

/-
**LinearPMap.instSub** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instSub : Sub (E ->ₛₗ.[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (E →ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain ≤ _))
        - g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain ≤ _)) }⟩
/-
**LinearPMap.sub_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：sub_domain (f g : E ->ₛₗ.[σ] F) : (f - g).domain = f.domain ⊓ g.domain
参数：f g : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_domain (f g : E →ₛₗ.[σ] F) : (f - g).domain = f.domain ⊓ g.domain := rfl
/-
**LinearPMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：sub_apply (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E))
 : (f - g) x = f ⟨x, x.prop.1⟩ - g ⟨x, x.prop.2⟩
参数：f g : E ->ₛₗ.[σ] F；x : (f.domain ⊓ g.domain : Submodule R E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f - g) x = f ⟨x, x.prop.1⟩ - g ⟨x, x.prop.2⟩ := rfl
/-
**LinearPMap.instSubtractionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instSubtractionCommMonoid : SubtractionCommMonoid (E ->ₛₗ.[σ] F) where add
_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSubtractionCommMonoid : SubtractionCommMonoid (E →ₛₗ.[σ] F) where
  add_comm := add_comm
  sub_eq_add_neg f g := by
    ext x _ h
    · rfl
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg]
  neg_neg := neg_neg
  neg_add_rev f g := by
    ext x _ h
    · simp [add_domain, neg_domain, And.comm]
    simp [add_apply, neg_apply, ← sub_eq_add_neg]
  neg_eq_of_add f g h' := by
    ext x hf hg
    · have : (0 : E →ₛₗ.[σ] F).domain = ⊤ := zero_domain
      simp only [← h', add_domain, inf_eq_top_iff] at this
      rw [neg_domain, this.1, this.2]
    simp only [neg_domain, neg_apply, neg_eq_iff_add_eq_zero]
    rw [ext_iff] at h'
    rcases h' with ⟨hdom, h'⟩
    rw [zero_domain] at hdom
    simp only [hdom, zero_domain, mem_top, zero_apply, forall_true_left] at h'
    apply h'
  zsmul := zsmulRec

end Sub

section

variable {K L : Type*} [DivisionRing K] [DivisionRing L] {σ : K →+* L} [Module K E] [Module L F]

/-- Extend a `LinearPMap` to `f.domain ⊔ K ∙ x`. -/
/-
**LinearPMap.supSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：supSpanSingleton (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) : 
E ->ₛₗ.[σ] F
参数：f : E ->ₛₗ.[σ] F；x : E；y : F；hx : x ∉ f.domain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a `LinearPMap` to `f.domain ⊔ K ∙ x`.
-/
noncomputable def supSpanSingleton (f : E →ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    E →ₛₗ.[σ] F :=
  f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem) <|
    sup_h_of_disjoint _ _ <| by simpa [disjoint_span_singleton] using fun h ↦ False.elim <| hx h

@[simp]
/-
**LinearPMap.domain_supSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domain_supSpanSingleton (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.dom
ain) : (f.supSpanSingleton x y hx).domain = f.domain ⊔ K ∙ x
参数：f : E ->ₛₗ.[σ] F；x : E；y : F；hx : x ∉ f.domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domain_supSpanSingleton (f : E →ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    (f.supSpanSingleton x y hx).domain = f.domain ⊔ K ∙ x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearPMap.supSpanSingleton_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：supSpanSingleton_apply_mk (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.d
omain) (x' : E) (hx' : x' in f.domain) (c : K) : f.supSpanSingleton x y hx ⟨x' +
 c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ = f ⟨x', hx'
⟩ + σ c • y
参数：f : E ->ₛₗ.[σ] F；x : E；y : F；hx : x ∉ f.domain；x' : E；hx' : x' in f.domain；c 
: K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.sup_apply`：sup_apply {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.
domain) (y : g.domain), (x : E) = y -> f x = g y) (x : f.domain) (y : g.domain) 
(z : ↥(f.d…
· 使用定理 `LinearPMap.mkSpanSingleton'_apply`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup
 E]   [inst_3 : _root_.…
-/
theorem supSpanSingleton_apply_mk (f : E →ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
    (hx' : x' ∈ f.domain) (c : K) :
    f.supSpanSingleton x y hx
        ⟨x' + c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
      f ⟨x', hx'⟩ + σ c • y := by
  unfold supSpanSingleton
  rw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mkSpanSingleton'_apply]
  · rfl
  · exact mem_span_singleton.2 ⟨c, rfl⟩

@[simp]
/-
**LinearPMap.supSpanSingleton_apply_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearP
Map`。
形式化陈述：supSpanSingleton_apply_smul_self (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : 
x ∉ f.domain) (c : K) : f.supSpanSingleton x y hx ⟨c • x, mem_sup_right mem_span
_singleton.2 ⟨c, rfl⟩⟩ = σ c • y
参数：f : E ->ₛₗ.[σ] F；y : F；hx : x ∉ f.domain；c : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mk_eq_zero`：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x
 = 0
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk`：supSpanSingleton_apply_mk (f : E -
>ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E) (hx' : x' in f.domain) (
c : K) : f.supSpanSingleto…
-/
theorem supSpanSingleton_apply_smul_self (f : E →ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (c : K) :
    f.supSpanSingleton x y hx ⟨c • x, mem_sup_right <| mem_span_singleton.2 ⟨c, rfl⟩⟩ =
      σ c • y := by
  simpa [(mk_eq_zero _ _).mpr rfl] using supSpanSingleton_apply_mk f x y hx 0 (zero_mem _) c

@[simp]
/-
**LinearPMap.supSpanSingleton_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：supSpanSingleton_apply_self (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f
.domain) : f.supSpanSingleton x y hx ⟨x, mem_sup_right mem_span_singleton_self _
⟩ = y
参数：f : E ->ₛₗ.[σ] F；y : F；hx : x ∉ f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LinearPMap.supSpanSingleton_apply_smul_self`：supSpanSingleton_apply_smul
_self (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) (c : K) : f.supSpan
Singleton x y hx ⟨c • x, mem_sup_…
-/
theorem supSpanSingleton_apply_self (f : E →ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) :
    f.supSpanSingleton x y hx ⟨x, mem_sup_right <| mem_span_singleton_self _⟩ = y := by
  simpa using supSpanSingleton_apply_smul_self f y hx 1

set_option backward.isDefEq.respectTransparency.types false in
/-
**LinearPMap.supSpanSingleton_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap
`。
形式化陈述：supSpanSingleton_apply_of_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉
 f.domain) (x' : (f.supSpanSingleton x y hx).domain) (hx' : (x' : E) in f.domain
) : f.supSpanSingleton x y hx x' = f ⟨x', hx'⟩
参数：f : E ->ₛₗ.[σ] F；y : F；hx : x ∉ f.domain；x' : (f.supSpanSingleton x y hx).dom
ain；hx' : (x' : E) in f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk`：supSpanSingleton_apply_mk (f : E -
>ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E) (hx' : x' in f.domain) (
c : K) : f.supSpanSingleto…
-/
theorem supSpanSingleton_apply_of_mem (f : E →ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (x' : (f.supSpanSingleton x y hx).domain) (hx' : (x' : E) ∈ f.domain) :
    f.supSpanSingleton x y hx x' = f ⟨x', hx'⟩ := by
  simpa using supSpanSingleton_apply_mk f x y hx x' hx' 0
/-
**LinearPMap.supSpanSingleton_apply_mk_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LinearP
Map`。
形式化陈述：supSpanSingleton_apply_mk_of_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : 
x ∉ f.domain) {x' : E} (hx' : (x' : E) in f.domain) : f.supSpanSingleton x y hx 
⟨x', mem_sup_left hx'⟩ = f ⟨x', hx'⟩
参数：f : E ->ₛₗ.[σ] F；y : F；hx : x ∉ f.domain；hx' : (x' : E) in f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.supSpanSingleton_apply_of_mem`：supSpanSingleton_apply_of_mem 
(f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) (x' : (f.supSpanSingleton
 x y hx).domain) (hx' : (x' : …
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
-/
theorem supSpanSingleton_apply_mk_of_mem (f : E →ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    {x' : E} (hx' : (x' : E) ∈ f.domain) :
    f.supSpanSingleton x y hx ⟨x', mem_sup_left hx'⟩ = f ⟨x', hx'⟩ :=
  supSpanSingleton_apply_of_mem f y hx _ hx'

end

set_option backward.privateInPublic true in
/-
**LinearPMap.sSup_aux** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sSup_aux (c : Set (E →ₛₗ.[σ] F)) (hc : DirectedOn (· ≤ ·) c) :
    ∃ f : ↥(sSup (domain '' c)) →ₛₗ[σ] F, (⟨_, f⟩ : E →ₛₗ.[σ] F) ∈ upperBounds c := by
  rcases c.eq_empty_or_nonempty with rfl | cne
  · simp
  have hdir : DirectedOn (· ≤ ·) (domain '' c) :=
    directedOn_image.2 (hc.mono @(domain_mono.monotone))
  have P : ∀ x : ↥(sSup (domain '' c)), { p : c // (x : E) ∈ p.val.domain } := by
    rintro x
    apply Classical.indefiniteDescription
    have := (mem_sSup_of_directed (cne.image _) hdir).1 x.2
    rwa [Set.exists_mem_image, ← bex_def, SetCoe.exists'] at this
  set f : ↥(sSup (domain '' c)) → F := fun x => (P x).val.val ⟨x, (P x).property⟩
  have f_eq : ∀ (p : c) (x : ↥(sSup (domain '' c))) (y : p.1.1) (_hxy : (x : E) = y),
      f x = p.1 y := by
    intro p x y hxy
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, _hqc, ⟨hxq1, hxq2⟩, ⟨hpq1, hpq2⟩⟩
    exact (hxq2 (y := ⟨y, hpq1 y.2⟩) hxy).trans (hpq2 rfl).symm
  use { toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_
  · intro x y
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩
    set x' := inclusion hpx.1 ⟨x, (P x).2⟩
    set y' := inclusion hpy.1 ⟨y, (P y).2⟩
    rw [f_eq ⟨p, hpc⟩ x x' rfl, f_eq ⟨p, hpc⟩ y y' rfl, f_eq ⟨p, hpc⟩ (x + y) (x' + y') rfl,
      map_add]
  · intro c x
    rw [f_eq (P x).1 (c • x) (c • ⟨x, (P x).2⟩) rfl, ← map_smulₛₗ]
  · intro p hpc
    refine ⟨le_sSup <| Set.mem_image_of_mem domain hpc, fun x y hxy => Eq.symm ?_⟩
    exact f_eq ⟨p, hpc⟩ _ _ hxy.symm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- For a family of (semi)linear maps with a directed domains such that the one defined on a larger
domain restricts to the one defined on the smaller domain, this defines the (semi)linear map defined
on the union of the domains extending all the (semi)linear maps in the family. -/
/-
**LinearPMap.sSup** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Ring R] →       [inst_1 : 
Ring S] →         {σ : R →+* S} →           {E : Type u_4} →             [inst_2
 : AddCommGroup E] →               [inst_3 : _root_.Module R E] →               
  {F : Type u_5} →                   [inst_4 : AddCommGroup F] →                
     [inst_5 : _root_.Module S F] →                       (c : Set (E →ₛₗ.[σ] F)
) → DirectedOn (fun x1 x2 => x1 ≤ x2) c → E →ₛₗ.[σ] F
参数：c : Set (E →ₛₗ.[σ] F)；fun x1 x2 => x1 ≤ x2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearPMap.0.LinearPMap.sSup_aux`：∀ {R : 
Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Ty
pe u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.…

--- 原说明 ---
For a family of (semi)linear maps with a directed domains such that the one defi
ned on a larger
domain restricts to the one defined on the smaller domain, this defines the (sem
i)linear map defined
on the union of the domains extending all the (semi)linear maps in the family.
-/
protected noncomputable def sSup (c : Set (E →ₛₗ.[σ] F)) (hc : DirectedOn (· ≤ ·) c) :
    E →ₛₗ.[σ] F :=
  ⟨_, Classical.choose <| sSup_aux c hc⟩
/-
**LinearPMap.domain_sSup** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domain_sSup {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) : (Linea
rPMap.sSup c hc).domain = sSup (LinearPMap.domain '' c)
参数：E ->ₛₗ.[σ] F；hc : DirectedOn (· <= ·) c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domain_sSup {c : Set (E →ₛₗ.[σ] F)} (hc : DirectedOn (· ≤ ·) c) :
    (LinearPMap.sSup c hc).domain = sSup (LinearPMap.domain '' c) := rfl
/-
**LinearPMap.mem_domain_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_domain_sSup_iff {c : Set (E ->ₛₗ.[σ] F)} (hnonempty : c.Nonempty) (hc 
: DirectedOn (· <= ·) c) {x : E} : x in (LinearPMap.sSup c hc).domain ↔ exists f
 in c, x in f.domain
参数：E ->ₛₗ.[σ] F；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.domain_sSup`：domain_sSup {c : Set (E ->ₛₗ.[σ] F)} (hc : Direc
tedOn (· <= ·) c) : (LinearPMap.sSup c hc).domain = sSup (LinearPMap.domain '' c
)
· 使用定理 `Submodule.mem_sSup_of_directed`：mem_sSup_of_directed {s : Set (Submodule
 R M)} {z} (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) : z in sSup s ↔ exis
ts y in s, z in y
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `LinearPMap.domain_mono`：domain_mono : StrictMono (domain (σ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_domain_sSup_iff {c : Set (E →ₛₗ.[σ] F)} (hnonempty : c.Nonempty)
    (hc : DirectedOn (· ≤ ·) c) {x : E} :
    x ∈ (LinearPMap.sSup c hc).domain ↔ ∃ f ∈ c, x ∈ f.domain := by
  rw [domain_sSup, Submodule.mem_sSup_of_directed (hnonempty.image _)
    (DirectedOn.mono_comp LinearPMap.domain_mono.monotone hc)]
  simp
/-
**LinearPMap.le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F]   {c : Set (
E →ₛₗ.[σ] F)} (hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c) {f : E →ₛₗ.[σ] F}, f ∈ 
c → f ≤ LinearPMap.sSup c hc
参数：E →ₛₗ.[σ] F；hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearPMap.0.LinearPMap.sSup_aux`：∀ {R : 
Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Ty
pe u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.…
-/
protected theorem le_sSup {c : Set (E →ₛₗ.[σ] F)} (hc : DirectedOn (· ≤ ·) c) {f : E →ₛₗ.[σ] F}
    (hf : f ∈ c) : f ≤ LinearPMap.sSup c hc :=
  Classical.choose_spec (sSup_aux c hc) hf
/-
**LinearPMap.sSup_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F]   {c : Set (
E →ₛₗ.[σ] F)} (hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c) {g : E →ₛₗ.[σ] F},   (∀
 f ∈ c, f ≤ g) → LinearPMap.sSup c hc ≤ g
参数：E →ₛₗ.[σ] F；hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c；∀ f ∈ c, f ≤ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_of_eqLocus_ge`：le_of_eqLocus_ge {f g : E ->ₛₗ.[σ] F} (H : 
f.domain <= f.eqLocus g) : f <= g
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `LinearPMap.le_sSup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [ins
t_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 :
 _root_.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem sSup_le {c : Set (E →ₛₗ.[σ] F)} (hc : DirectedOn (· ≤ ·) c) {g : E →ₛₗ.[σ] F}
    (hg : ∀ f ∈ c, f ≤ g) : LinearPMap.sSup c hc ≤ g :=
  le_of_eqLocus_ge <|
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f ≤ LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1
/-
**LinearPMap.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →
+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module R E] {F
 : Type u_5} [inst_4 : AddCommGroup F] [inst_5 : _root_.Module S F]   {c : Set (
E →ₛₗ.[σ] F)} (hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c) {l : E →ₛₗ.[σ] F} (hl :
 l ∈ c) (x : ↥l.domain),   ↑(LinearPMap.sSup c hc) ⟨↑x, ⋯⟩ = ↑l x
参数：E →ₛₗ.[σ] F；hc : DirectedOn (fun x1 x2 => x1 ≤ x2) c；hl : l ∈ c；x : ↥l.domain
；LinearPMap.sSup c hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearPMap.le_sSup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [ins
t_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 :
 _root_.…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearPMap.0.LinearPMap.sSup_aux`：∀ {R : 
Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Ty
pe u_4} [inst_2 : AddCommGroup E]   [inst_3 : _root_.…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem sSup_apply {c : Set (E →ₛₗ.[σ] F)} (hc : DirectedOn (· ≤ ·) c) {l : E →ₛₗ.[σ] F}
    (hl : l ∈ c) (x : l.domain) :
    (LinearPMap.sSup c hc) ⟨x, (LinearPMap.le_sSup hc hl).1 x.2⟩ = l x := by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl

end LinearPMap

namespace LinearMap

/-- Restrict a linear map to a submodule, reinterpreting the result as a `LinearPMap`. -/
/-
**LinearMap.toPMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toPMap (f : E ->ₛₗ[σ] F) (p : Submodule R E) : E ->ₛₗ.[σ] F
参数：f : E ->ₛₗ[σ] F；p : Submodule R E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a linear map to a submodule, reinterpreting the result as a `LinearPMap
`.
-/
def toPMap (f : E →ₛₗ[σ] F) (p : Submodule R E) : E →ₛₗ.[σ] F :=
  ⟨p, f.comp p.subtype⟩

@[simp]
/-
**LinearMap.toPMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toPMap_apply (f : E ->ₛₗ[σ] F) (p : Submodule R E) (x : p) : f.toPMap p x 
= f x
参数：f : E ->ₛₗ[σ] F；p : Submodule R E；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPMap_apply (f : E →ₛₗ[σ] F) (p : Submodule R E) (x : p) : f.toPMap p x = f x :=
  rfl

@[simp]
/-
**LinearMap.toPMap_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toPMap_domain (f : E ->ₛₗ[σ] F) (p : Submodule R E) : (f.toPMap p).domain 
= p
参数：f : E ->ₛₗ[σ] F；p : Submodule R E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPMap_domain (f : E →ₛₗ[σ] F) (p : Submodule R E) : (f.toPMap p).domain = p :=
  rfl

/-- Compose a linear map with a `LinearPMap` -/
/-
**LinearMap.compPMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compPMap {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ[τ] G) (f : E
 ->ₛₗ.[σ] F) : E ->ₛₗ.[ρ] G where domain
参数：g : F ->ₛₗ[τ] G；f : E ->ₛₗ.[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a linear map with a `LinearPMap`
-/
def compPMap {ρ : R →+* T} [RingHomCompTriple σ τ ρ] (g : F →ₛₗ[τ] G) (f : E →ₛₗ.[σ] F) :
    E →ₛₗ.[ρ] G where
  domain := f.domain
  toFun := g.comp f.toFun

@[simp]
/-
**LinearMap.compPMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compPMap_apply (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F) (x) : letI : RingHomCo
mpTriple σ τ (τ.comp σ)
参数：g : F ->ₛₗ[τ] G；f : E ->ₛₗ.[σ] F；x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compPMap_apply (g : F →ₛₗ[τ] G) (f : E →ₛₗ.[σ] F) (x) :
    letI : RingHomCompTriple σ τ (τ.comp σ) := { comp_eq := rfl }
    g.compPMap (ρ := τ.comp σ) f x = g (f x) :=
  rfl

end LinearMap

namespace LinearPMap

/-- Restrict codomain of a `LinearPMap` -/
/-
**LinearPMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：codRestrict (f : E ->ₛₗ.[σ] F) (p : Submodule S F) (H : forall x, f x in p
) : E ->ₛₗ.[σ] p where domain
参数：f : E ->ₛₗ.[σ] F；p : Submodule S F；H : forall x, f x in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict codomain of a `LinearPMap`
-/
def codRestrict (f : E →ₛₗ.[σ] F) (p : Submodule S F) (H : ∀ x, f x ∈ p) : E →ₛₗ.[σ] p where
  domain := f.domain
  toFun := f.toFun.codRestrict p H

/-- Compose two `LinearPMap`s -/
/-
**LinearPMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：comp {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ.[τ] G) (f : E ->
ₛₗ.[σ] F) (H : forall x : f.domain, f x in g.domain) : E ->ₛₗ.[ρ] G
参数：g : F ->ₛₗ.[τ] G；f : E ->ₛₗ.[σ] F；H : forall x : f.domain, f x in g.domain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two `LinearPMap`s
-/
def comp {ρ : R →+* T} [RingHomCompTriple σ τ ρ] (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F)
    (H : ∀ x : f.domain, f x ∈ g.domain) : E →ₛₗ.[ρ] G :=
  g.toFun.compPMap <| f.codRestrict _ H

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
/-
**LinearPMap.coprod** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：coprod [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G) : E
 × F ->ₛₗ.[σ] G where domain
参数：f : E ->ₛₗ.[σ] G；g : F ->ₛₗ.[σ] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.coprod g` is the partially defined linear map defined on `f.domain × g.domain
`,
and sending `p` to `f p.1 + g p.2`.
-/
def coprod [Module R F] [Module S G] (f : E →ₛₗ.[σ] G) (g : F →ₛₗ.[σ] G) : E × F →ₛₗ.[σ] G where
  domain := f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain →ₛₗ[σ] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain →ₛₗ[σ] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

omit [Module S F] in
@[simp]
/-
**LinearPMap.coprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：coprod_apply [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] 
G) (x) : f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩
参数：f : E ->ₛₗ.[σ] G；g : F ->ₛₗ.[σ] G；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprod_apply [Module R F] [Module S G] (f : E →ₛₗ.[σ] G) (g : F →ₛₗ.[σ] G) (x) :
    f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl

/-- Restrict a partially defined linear map to a submodule of `E` contained in `f.domain`. -/
/-
**LinearPMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：domRestrict (f : E ->ₛₗ.[σ] F) (S : Submodule R E) : E ->ₛₗ.[σ] F
参数：f : E ->ₛₗ.[σ] F；S : Submodule R E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a partially defined linear map to a submodule of `E` contained in `f.do
main`.
-/
def domRestrict (f : E →ₛₗ.[σ] F) (S : Submodule R E) : E →ₛₗ.[σ] F :=
  ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩

@[simp]
/-
**LinearPMap.domRestrict_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domRestrict_domain (f : E ->ₛₗ.[σ] F) {S : Submodule R E} : (f.domRestrict
 S).domain = S ⊓ f.domain
参数：f : E ->ₛₗ.[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_domain (f : E →ₛₗ.[σ] F) {S : Submodule R E} :
    (f.domRestrict S).domain = S ⊓ f.domain :=
  rfl
/-
**LinearPMap.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domRestrict_apply {f : E ->ₛₗ.[σ] F} {S : Submodule R E} ⦃x : ↥(S ⊓ f.doma
in)⦄ ⦃y : f.domain⦄ (h : (x : E) = y) : f.domRestrict S x = f y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.mk_apply`：mk_apply (p : Submodule R E) (f : p ->ₛₗ[σ] F) (x :
 p) : mk p f x = f x
-/
theorem domRestrict_apply {f : E →ₛₗ.[σ] F} {S : Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
    (h : (x : E) = y) : f.domRestrict S x = f y := by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _
/-
**LinearPMap.domRestrict_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：domRestrict_le {f : E ->ₛₗ.[σ] F} {S : Submodule R E} : f.domRestrict S <=
 f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearPMap.domRestrict_apply`：domRestrict_apply {f : E ->ₛₗ.[σ] F} {S : 
Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄ (h : (x : E) = y) : f.domRes
trict S x = f y
-/
theorem domRestrict_le {f : E →ₛₗ.[σ] F} {S : Submodule R E} : f.domRestrict S ≤ f :=
  ⟨by simp, fun _ _ hxy => domRestrict_apply hxy⟩

/-! ### Graph -/


section Graph

/-- The graph of a `LinearPMap` viewed as a submodule on `E × F`. -/
/-
**LinearPMap.graph** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：graph [Module R F] (f : E ->ₗ.[R] F) : Submodule R (E × F)
参数：f : E ->ₗ.[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph of a `LinearPMap` viewed as a submodule on `E × F`.
-/
def graph [Module R F] (f : E →ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F →ₗ[R] F))
/-
**LinearPMap.mem_graph_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_graph_iff' [Module R F] (f : E ->ₗ.[R] F) {x : E × F} : x in f.graph ↔
 exists y : f.domain, (↑y, f y) = x
参数：f : E ->ₗ.[R] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_graph_iff' [Module R F] (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y, f y) = x := by simp [graph]

@[simp, grind =]
/-
**LinearPMap.mem_graph_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {x : E × F} : x in f.graph ↔ 
exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2
参数：f : E ->ₗ.[R] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_graph_iff [Module R F] (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y : E) = x.1 ∧ f y = x.2 := by
  cases x
  simp_rw [mem_graph_iff', Prod.mk_inj]

/-- The tuple `(x, f x)` is contained in the graph of `f`. -/
/-
**LinearPMap.mem_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_graph [Module R F] (f : E ->ₗ.[R] F) (x : domain f) : ((x : E), f x) i
n f.graph
参数：f : E ->ₗ.[R] F；x : domain f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The tuple `(x, f x)` is contained in the graph of `f`.
-/
theorem mem_graph [Module R F] (f : E →ₗ.[R] F) (x : domain f) : ((x : E), f x) ∈ f.graph := by simp
/-
**LinearPMap.graph_map_fst_eq_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：graph_map_fst_eq_domain [Module R F] (f : E ->ₗ.[R] F) : f.graph.map (Line
arMap.fst R E F) = f.domain
参数：f : E ->ₗ.[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem graph_map_fst_eq_domain [Module R F] (f : E →ₗ.[R] F) :
    f.graph.map (LinearMap.fst R E F) = f.domain := by
  ext x
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor <;> intro h
  · rcases h with ⟨x, hx, _⟩
    exact hx
  · use f ⟨x, h⟩
    simp only [h, exists_const]
/-
**LinearPMap.graph_map_snd_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：graph_map_snd_eq_range [Module R F] (f : E ->ₗ.[R] F) : f.graph.map (Linea
rMap.snd R E F) = LinearMap.range f.toFun
参数：f : E ->ₗ.[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem graph_map_snd_eq_range [Module R F] (f : E →ₗ.[R] F) :
    f.graph.map (LinearMap.snd R E F) = LinearMap.range f.toFun := by ext; simp

variable {M : Type*} [Monoid M] [DistribMulAction M F] [Module R F] [SMulCommClass R M F] (y : M)

/-- The graph of `z • f` as a pushforward. -/
/-
**LinearPMap.smul_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：smul_graph (f : E ->ₗ.[R] F) (z : M) : (z • f).graph = f.graph.map ((Linea
rMap.id : E ->ₗ[R] E).prodMap (z • (LinearMap.id : F ->ₗ[R] F)))
参数：f : E ->ₗ.[R] F；z : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_graph_iff`：mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {
x : E × F} : x in f.graph ↔ exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearPMap.smul_apply`：smul_apply (a : M) (f : E ->ₛₗ.[σ] F) (x : (a • f
).domain) : (a • f) x = a • f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The graph of `z • f` as a pushforward.
-/
theorem smul_graph (f : E →ₗ.[R] F) (z : M) :
    (z • f).graph =
      f.graph.map ((LinearMap.id : E →ₗ[R] E).prodMap (z • (LinearMap.id : F →ₗ[R] F))) := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.smul_apply, Prod.mk_inj, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.smul_apply,
    Prod.mk_inj] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']

/-- The graph of `-f` as a pushforward. -/
/-
**LinearPMap.neg_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：neg_graph (f : E ->ₗ.[R] F) : (-f).graph = f.graph.map ((LinearMap.id : E 
->ₗ[R] E).prodMap (-(LinearMap.id : F ->ₗ[R] F)))
参数：f : E ->ₗ.[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_graph_iff`：mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {
x : E × F} : x in f.graph ↔ exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearPMap.neg_apply`：neg_apply (f : E ->ₛₗ.[σ] F) (x) : (-f) x = -f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The graph of `-f` as a pushforward.
-/
theorem neg_graph (f : E →ₗ.[R] F) :
    (-f).graph =
    f.graph.map ((LinearMap.id : E →ₗ[R] E).prodMap (-(LinearMap.id : F →ₗ[R] F))) := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.neg_apply, Prod.mk_inj, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.neg_apply,
    Prod.mk_inj] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']
/-
**LinearPMap.mem_graph_snd_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_graph_snd_inj (f : E ->ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') in
 f.graph) (hy : (y, y') in f.graph) (hxy : x = y) : x' = y'
参数：f : E ->ₗ.[R] F；hx : (x, x') in f.graph；hy : (y, y') in f.graph；hxy : x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_graph_snd_inj (f : E →ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') ∈ f.graph)
    (hy : (y, y') ∈ f.graph) (hxy : x = y) : x' = y' := by
  grind
/-
**LinearPMap.mem_graph_snd_inj'** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_graph_snd_inj' (f : E ->ₗ.[R] F) {x y : E × F} (hx : x in f.graph) (hy
 : y in f.graph) (hxy : x.1 = y.1) : x.2 = y.2
参数：f : E ->ₗ.[R] F；hx : x in f.graph；hy : y in f.graph；hxy : x.1 = y.1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_graph_snd_inj' (f : E →ₗ.[R] F) {x y : E × F} (hx : x ∈ f.graph) (hy : y ∈ f.graph)
    (hxy : x.1 = y.1) : x.2 = y.2 := by
  grind

/-- The property that `f 0 = 0` in terms of the graph. -/
/-
**LinearPMap.graph_fst_eq_zero_snd** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：graph_fst_eq_zero_snd (f : E ->ₗ.[R] F) {x : E} {x' : F} (h : (x, x') in f
.graph) (hx : x = 0) : x' = 0
参数：f : E ->ₗ.[R] F；h : (x, x') in f.graph；hx : x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.mem_graph_snd_inj`：mem_graph_snd_inj (f : E ->ₗ.[R] F) {x y :
 E} {x' y' : F} (hx : (x, x') in f.graph) (hy : (y, y') in f.graph) (hxy : x = y
) : x' = y'
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p

--- 原说明 ---
The property that `f 0 = 0` in terms of the graph.
-/
theorem graph_fst_eq_zero_snd (f : E →ₗ.[R] F) {x : E} {x' : F} (h : (x, x') ∈ f.graph)
    (hx : x = 0) : x' = 0 :=
  f.mem_graph_snd_inj h f.graph.zero_mem hx
/-
**LinearPMap.mem_domain_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_domain_iff {f : E ->ₗ.[R] F} {x : E} : x in f.domain ↔ exists y : F, (
x, y) in f.graph
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.mem_graph`：mem_graph [Module R F] (f : E ->ₗ.[R] F) (x : doma
in f) : ((x : E), f x) in f.graph
-/
theorem mem_domain_iff {f : E →ₗ.[R] F} {x : E} : x ∈ f.domain ↔ ∃ y : F, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  grind
/-
**LinearPMap.mem_domain_of_mem_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_domain_of_mem_graph {f : E ->ₗ.[R] F} {x : E} {y : F} (h : (x, y) in f
.graph) : x in f.domain
参数：h : (x, y) in f.graph。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_domain_iff`：mem_domain_iff {f : E ->ₗ.[R] F} {x : E} : x 
in f.domain ↔ exists y : F, (x, y) in f.graph
-/
theorem mem_domain_of_mem_graph {f : E →ₗ.[R] F} {x : E} {y : F} (h : (x, y) ∈ f.graph) :
    x ∈ f.domain := by
  rw [mem_domain_iff]
  exact ⟨y, h⟩
/-
**LinearPMap.image_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：image_iff {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : x in f.domain) : y = f ⟨
x, hx⟩ ↔ (x, y) in f.graph
参数：hx : x in f.domain。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_iff {f : E →ₗ.[R] F} {x : E} {y : F} (hx : x ∈ f.domain) :
    y = f ⟨x, hx⟩ ↔ (x, y) ∈ f.graph := by
  grind
/-
**LinearPMap.mem_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_range_iff {f : E ->ₗ.[R] F} {y : F} : y in Set.range f ↔ exists x : E,
 (x, y) in f.graph
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.mem_graph`：mem_graph [Module R F] (f : E ->ₗ.[R] F) (x : doma
in f) : ((x : E), f x) in f.graph
-/
theorem mem_range_iff {f : E →ₗ.[R] F} {y : F} : y ∈ Set.range f ↔ ∃ x : E, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  grind
/-
**LinearPMap.mem_domain_iff_of_eq_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_domain_iff_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) {x 
: E} : x in f.domain ↔ x in g.domain
参数：h : f.graph = g.graph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_domain_iff_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) {x : E} :
    x ∈ f.domain ↔ x ∈ g.domain := by simp_rw [mem_domain_iff, h]
/-
**LinearPMap.le_of_le_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.graph <= g.graph) : f <= g
参数：h : f.graph <= g.graph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_domain_iff`：mem_domain_iff {f : E ->ₗ.[R] F} {x : E} : x 
in f.domain ↔ exists y : F, (x, y) in f.graph
· 使用定理 `LinearPMap.image_iff`：image_iff {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : 
x in f.domain) : y = f ⟨x, hx⟩ ↔ (x, y) in f.graph
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_of_le_graph {f g : E →ₗ.[R] F} (h : f.graph ≤ g.graph) : f ≤ g := by
  constructor
  · intro x hx
    rw [mem_domain_iff] at hx ⊢
    obtain ⟨y, hx⟩ := hx
    use y
    exact h hx
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [image_iff]
  refine h ?_
  simp only at hxy
  rw [hxy] at hx
  rw [← image_iff hx]
  simp [hxy]
/-
**LinearPMap.le_graph_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：le_graph_of_le {f g : E ->ₗ.[R] F} (h : f <= g) : f.graph <= g.graph
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_graph_iff`：mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {
x : E × F} : x in f.graph ↔ exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem le_graph_of_le {f g : E →ₗ.[R] F} (h : f ≤ g) : f.graph ≤ g.graph := by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert! hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]
/-
**LinearPMap.le_graph_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：le_graph_iff {f g : E ->ₗ.[R] F} : f.graph <= g.graph ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_of_le_graph`：le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph <= g.graph) : f <= g
· 使用定理 `LinearPMap.le_graph_of_le`：le_graph_of_le {f g : E ->ₗ.[R] F} (h : f <= 
g) : f.graph <= g.graph
-/
theorem le_graph_iff {f g : E →ₗ.[R] F} : f.graph ≤ g.graph ↔ f ≤ g :=
  ⟨le_of_le_graph, le_graph_of_le⟩
/-
**LinearPMap.eq_of_eq_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：eq_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) : f = g
参数：h : f.graph = g.graph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.dExt`：dExt {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h'
 : forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `LinearPMap.mem_domain_iff_of_eq_graph`：mem_domain_iff_of_eq_graph {f g :
 E ->ₗ.[R] F} (h : f.graph = g.graph) {x : E} : x in f.domain ↔ x in g.domain
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearPMap.le_of_le_graph`：le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph <= g.graph) : f <= g
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem eq_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) : f = g := by
  apply dExt
  · ext
    exact mem_domain_iff_of_eq_graph h
  · apply (le_of_le_graph h.le).2

end Graph

end LinearPMap

namespace Submodule

section SubmoduleToLinearPMap

variable [Module R F]

/-
**Submodule.existsUnique_from_graph** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：existsUnique_from_graph {g : Submodule R (E × F)} (hg : forall {x : E × F}
 (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E} (ha : a in g.map (LinearM
ap.fst R E F)) : exists! b : F, (a, b) in g
参数：E × F；hg : forall {x : E × F} (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0；ha
 : a in g.map (LinearMap.fst R E F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem existsUnique_from_graph {g : Submodule R (E × F)}
    (hg : ∀ {x : E × F} (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : ∃! b : F, (a, b) ∈ g := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · convert! ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) ∈ g := by
    convert! g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))

/-- Auxiliary definition to unfold the existential quantifier. -/
/-
**Submodule.valFromGraph** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：valFromGraph {g : Submodule R (E × F)} (hg : forall (x : E × F) (_hx : x i
n g) (_hx' : x.fst = 0), x.snd = 0) {a : E} (ha : a in g.map (LinearMap.fst R E 
F)) : F
参数：E × F；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0；ha
 : a in g.map (LinearMap.fst R E F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to unfold the existential quantifier.
-/
noncomputable def valFromGraph {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : F :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose
/-
**Submodule.valFromGraph_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：valFromGraph_mem {g : Submodule R (E × F)} (hg : forall (x : E × F) (_hx :
 x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E} (ha : a in g.map (LinearMap.fst 
R E F)) : (a, valFromGraph hg ha) in g
参数：E × F；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0；ha
 : a in g.map (LinearMap.fst R E F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Submodule.existsUnique_from_graph`：existsUnique_from_graph {g : Submodul
e R (E × F)} (hg : forall {x : E × F} (_hx : x in g) (_hx' : x.fst = 0), x.snd =
 0) {a : E} (ha : a in …
-/
theorem valFromGraph_mem {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : (a, valFromGraph hg ha) ∈ g :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec

/-- Define a `LinearMap` from its graph.

Helper definition for `LinearPMap`. -/
/-
**Submodule.toLinearPMapAux** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toLinearPMapAux (g : Submodule R (E × F)) (hg : forall (x : E × F) (_hx : 
x in g) (_hx' : x.fst = 0), x.snd = 0) : g.map (LinearMap.fst R E F) ->ₗ[R] F wh
ere toFun
参数：g : Submodule R (E × F)；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst 
= 0), x.snd = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a `LinearMap` from its graph.

Helper definition for `LinearPMap`.
-/
noncomputable def toLinearPMapAux (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.map (LinearMap.fst R E F) →ₗ[R] F where
  toFun := fun x => valFromGraph hg x.2
  map_add' := fun v w => by
    have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
    have hvw := valFromGraph_mem hg hadd
    have hvw' := g.add_mem (valFromGraph_mem hg v.2) (valFromGraph_mem hg w.2)
    rw [Prod.mk_add_mk] at hvw'
    exact (existsUnique_from_graph @hg hadd).unique hvw hvw'
  map_smul' := fun a v => by
    have hsmul := (g.map (LinearMap.fst R E F)).smul_mem a v.2
    have hav := valFromGraph_mem hg hsmul
    have hav' := g.smul_mem a (valFromGraph_mem hg v.2)
    rw [Prod.smul_mk] at hav'
    exact (existsUnique_from_graph @hg hsmul).unique hav hav'

open scoped Classical in
/-- Define a `LinearPMap` from its graph.

In the case that the submodule is not a graph of a `LinearPMap` then the underlying linear map
is just the zero map. -/
/-
**Submodule.toLinearPMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toLinearPMap (g : Submodule R (E × F)) : E ->ₗ.[R] F where domain
参数：g : Submodule R (E × F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a `LinearPMap` from its graph.

In the case that the submodule is not a graph of a `LinearPMap` then the underly
ing linear map
is just the zero map.
-/
noncomputable def toLinearPMap (g : Submodule R (E × F)) : E →ₗ.[R] F where
  domain := g.map (LinearMap.fst R E F)
  toFun := if hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0
/-
**Submodule.toLinearPMap_domain** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearPMap_domain (g : Submodule R (E × F)) : g.toLinearPMap.domain = g.
map (LinearMap.fst R E F)
参数：g : Submodule R (E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearPMap_domain (g : Submodule R (E × F)) :
    g.toLinearPMap.domain = g.map (LinearMap.fst R E F) := rfl
/-
**Submodule.toLinearPMap_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearPMap_apply_aux {g : Submodule R (E × F)} (hg : forall (x : E × F) 
(_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) (x : g.map (LinearMap.fst R E F)) 
: g.toLinearPMap x = valFromGraph hg x.2
参数：E × F；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0；x 
: g.map (LinearMap.fst R E F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem toLinearPMap_apply_aux {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) :
    g.toLinearPMap x = valFromGraph hg x.2 := by
  classical
  change (if hg : _ then g.toLinearPMapAux hg else 0) x = _
  rw [dif_pos]
  · rfl
  · exact hg
/-
**Submodule.mem_graph_toLinearPMap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_graph_toLinearPMap {g : Submodule R (E × F)} (hg : forall (x : E × F) 
(_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) (x : g.map (LinearMap.fst R E F)) 
: (x.val, g.toLinearPMap x) in g
参数：E × F；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0；x 
: g.map (LinearMap.fst R E F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.toLinearPMap_apply_aux`：toLinearPMap_apply_aux {g : Submodule 
R (E × F)} (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0
) (x : g.map (LinearMa…
· 使用定理 `Submodule.valFromGraph_mem`：valFromGraph_mem {g : Submodule R (E × F)} (
hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E} (h
a : a in g.map (…
-/
theorem mem_graph_toLinearPMap {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) : (x.val, g.toLinearPMap x) ∈ g := by
  rw [toLinearPMap_apply_aux hg]
  exact valFromGraph_mem hg x.2

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Submodule.toLinearPMap_graph_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearPMap_graph_eq (g : Submodule R (E × F)) (hg : forall (x : E × F) (
_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) : g.toLinearPMap.graph = g
参数：g : Submodule R (E × F)；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst 
= 0), x.snd = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_graph_iff`：mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {
x : E × F} : x in f.graph ↔ exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Submodule.mem_graph_toLinearPMap`：mem_graph_toLinearPMap {g : Submodule 
R (E × F)} (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0
) (x : g.map (LinearMa…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.toLinearPMap_apply_aux`：toLinearPMap_apply_aux {g : Submodule 
R (E × F)} (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0
) (x : g.map (LinearMa…
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Submodule.existsUnique_from_graph`：existsUnique_from_graph {g : Submodul
e R (E × F)} (hg : forall {x : E × F} (_hx : x in g) (_hx' : x.fst = 0), x.snd =
 0) {a : E} (ha : a in …
· 使用定理 `Submodule.valFromGraph_mem`：valFromGraph_mem {g : Submodule R (E × F)} (
hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E} (h
a : a in g.map (…
-/
theorem toLinearPMap_graph_eq (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.toLinearPMap.graph = g := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert! g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  have hx_fst : x_fst ∈ g.map (LinearMap.fst R E F) := by
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨x_snd, hx⟩
  refine ⟨⟨x_fst, hx_fst⟩, Subtype.coe_mk x_fst hx_fst, ?_⟩
  rw [toLinearPMap_apply_aux hg]
  exact (existsUnique_from_graph @hg hx_fst).unique (valFromGraph_mem hg hx_fst) hx
/-
**Submodule.toLinearPMap_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearPMap_range (g : Submodule R (E × F)) (hg : forall (x : E × F) (_hx
 : x in g) (_hx' : x.fst = 0), x.snd = 0) : LinearMap.range g.toLinearPMap.toFun
 = g.map (LinearMap.snd R E F)
参数：g : Submodule R (E × F)；hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst 
= 0), x.snd = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.graph_map_snd_eq_range`：graph_map_snd_eq_range [Module R F] (
f : E ->ₗ.[R] F) : f.graph.map (LinearMap.snd R E F) = LinearMap.range f.toFun
· 使用定理 `Submodule.toLinearPMap_graph_eq`：toLinearPMap_graph_eq (g : Submodule R 
(E × F)) (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) 
: g.toLinearPMap.grap…
-/
theorem toLinearPMap_range (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    LinearMap.range g.toLinearPMap.toFun = g.map (LinearMap.snd R E F) := by
  rwa [← LinearPMap.graph_map_snd_eq_range, toLinearPMap_graph_eq]

end SubmoduleToLinearPMap

end Submodule

namespace LinearPMap

section inverse

variable [Module R F]

/-- The inverse of a `LinearPMap`. -/
/-
**LinearPMap.inverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：inverse (f : E ->ₗ.[R] F) : F ->ₗ.[R] E
参数：f : E ->ₗ.[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a `LinearPMap`.
-/
noncomputable def inverse (f : E →ₗ.[R] F) : F →ₗ.[R] E :=
  (f.graph.map (LinearEquiv.prodComm R E F : (E × F) →ₗ[R] (F × E))).toLinearPMap

variable {f : E →ₗ.[R] F}
/-
**LinearPMap.inverse_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_domain : (inverse f).domain = LinearMap.range f.toFun
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.inverse.eq_1`：∀ {R : Type u_1} [inst : Ring R] {E : Type u_4}
 [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {F : Type u_5}   [inst_3
 : AddCommGro…
· 使用定理 `Submodule.toLinearPMap_domain`：toLinearPMap_domain (g : Submodule R (E ×
 F)) : g.toLinearPMap.domain = g.map (LinearMap.fst R E F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.graph_map_snd_eq_range`：graph_map_snd_eq_range [Module R F] (
f : E ->ₗ.[R] F) : f.graph.map (LinearMap.snd R E F) = LinearMap.range f.toFun
· 使用定理 `LinearEquiv.fst_comp_prodComm`：fst_comp_prodComm : (LinearMap.fst R M₂ M
).comp (prodComm R M M₂).toLinearMap = (LinearMap.snd R M M₂)
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
-/
theorem inverse_domain : (inverse f).domain = LinearMap.range f.toFun := by
  rw [inverse, Submodule.toLinearPMap_domain, ← graph_map_snd_eq_range,
    ← LinearEquiv.fst_comp_prodComm, Submodule.map_comp]

variable (hf : f.toFun.ker = ⊥)
include hf

/-- The graph of the inverse generates a `LinearPMap`. -/
/-
**LinearPMap.mem_inverse_graph_snd_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap
`。
形式化陈述：mem_inverse_graph_snd_eq_zero (x : F × E) (hv : x in (graph f).map (Linear
Equiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))) (hv' : x.fst = 0) : x.snd = 0
参数：x : F × E；hv : x in (graph f).map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R
] (F × E))；hv' : x.fst = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The graph of the inverse generates a `LinearPMap`.
-/
theorem mem_inverse_graph_snd_eq_zero (x : F × E)
    (hv : x ∈ (graph f).map (LinearEquiv.prodComm R E F : (E × F) →ₗ[R] (F × E)))
    (hv' : x.fst = 0) : x.snd = 0 := by
  rcases x with ⟨x, y⟩
  subst hv'
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.symm_prodComm,
    LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, mem_graph_iff, Prod.swap] at hv
  rcases hv with ⟨z, rfl, hz⟩
  rw [LinearMap.ker_eq_bot'] at hf
  simp [hf z hz]
/-
**LinearPMap.inverse_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_graph : (inverse f).graph = f.graph.map (LinearEquiv.prodComm R E 
F : (E × F) ->ₗ[R] (F × E))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.inverse.eq_1`：∀ {R : Type u_1} [inst : Ring R] {E : Type u_4}
 [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {F : Type u_5}   [inst_3
 : AddCommGro…
· 使用定理 `Submodule.toLinearPMap_graph_eq`：toLinearPMap_graph_eq (g : Submodule R 
(E × F)) (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) 
: g.toLinearPMap.grap…
· 使用定理 `LinearPMap.mem_inverse_graph_snd_eq_zero`：mem_inverse_graph_snd_eq_zero 
(x : F × E) (hv : x in (graph f).map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R
] (F × E))) (hv' : x.fst = 0) …
-/
theorem inverse_graph :
    (inverse f).graph = f.graph.map (LinearEquiv.prodComm R E F : (E × F) →ₗ[R] (F × E)) := by
  rw [inverse, Submodule.toLinearPMap_graph_eq _ (mem_inverse_graph_snd_eq_zero hf)]
/-
**LinearPMap.inverse_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_range : LinearMap.range (inverse f).toFun = f.domain
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.inverse.eq_1`：∀ {R : Type u_1} [inst : Ring R] {E : Type u_4}
 [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {F : Type u_5}   [inst_3
 : AddCommGro…
· 使用定理 `Submodule.toLinearPMap_range`：toLinearPMap_range (g : Submodule R (E × F
)) (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) : Line
arMap.range g.toLi…
· 使用定理 `LinearPMap.mem_inverse_graph_snd_eq_zero`：mem_inverse_graph_snd_eq_zero 
(x : F × E) (hv : x in (graph f).map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R
] (F × E))) (hv' : x.fst = 0) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.graph_map_fst_eq_domain`：graph_map_fst_eq_domain [Module R F]
 (f : E ->ₗ.[R] F) : f.graph.map (LinearMap.fst R E F) = f.domain
· 使用定理 `LinearEquiv.snd_comp_prodComm`：snd_comp_prodComm : (LinearMap.snd R M₂ M
).comp (prodComm R M M₂).toLinearMap = (LinearMap.fst R M M₂)
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
-/
theorem inverse_range : LinearMap.range (inverse f).toFun = f.domain := by
  rw [inverse, Submodule.toLinearPMap_range _ (mem_inverse_graph_snd_eq_zero hf),
    ← graph_map_fst_eq_domain, ← LinearEquiv.snd_comp_prodComm, Submodule.map_comp]
/-
**LinearPMap.mem_inverse_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_inverse_graph (x : f.domain) : (f x, (x : E)) in (inverse f).graph
参数：x : f.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.inverse_graph`：inverse_graph : (inverse f).graph = f.graph.ma
p (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_inverse_graph (x : f.domain) : (f x, (x : E)) ∈ (inverse f).graph := by
  simp only [inverse_graph hf, Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  exact ⟨(x : E), f x, ⟨x.2, Eq.refl _⟩, Eq.refl _, Eq.refl _⟩
/-
**LinearPMap.inverse_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_apply_eq {y : (inverse f).domain} {x : f.domain} (hxy : f x = y) :
 (inverse f) y = x
参数：inverse f；hxy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.mem_inverse_graph`：mem_inverse_graph (x : f.domain) : (f x, (
x : E)) in (inverse f).graph
-/
theorem inverse_apply_eq {y : (inverse f).domain} {x : f.domain} (hxy : f x = y) :
    (inverse f) y = x := by
  have := mem_inverse_graph hf x
  grind

end inverse

end LinearPMap

