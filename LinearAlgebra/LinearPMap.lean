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

/--
Definition of `LinearPMap` / `LinearPMap` 的定义

English:
structure LinearPMap
  parameters: {R S : Type*} [Ring R] [Ring S] (σ : R ->+* S) (E : Type*)
  axioms and operations (2):
    - domain : Submodule R E
    - toFun : domain ->ₛₗ[σ] F

中文:
结构 LinearP映射
  参数: {R S : 类型} [环 R] [环 S] (σ : R ->+* S) (E : 类型)
  公理与运算 (2 个):
    - domain : 子模 R E
    - toFun : domain ->ₛₗ[σ] F
-/
structure LinearPMap {R S : Type*} [Ring R] [Ring S] (σ : R ->+* S) (E : Type*)
    [AddCommGroup E] [Module R E] (F : Type*) [AddCommGroup F] [Module S F] where
  /-- The domain of the (semi)linear map. -/
  domain : Submodule R E
  /-- The (semi)linear map itself. -/
  toFun : domain ->ₛₗ[σ] F

@[inherit_doc] notation:25 E " ->ₛₗ.[" σ:25 "] " F:0 => LinearPMap σ E F

/-- `E →ₗ.[R] F` is the notation for `E →ₛₗ.[RingHom.id R] F`. -/
notation:25 E " ->ₗ.[" R:25 "] " F:0 => LinearPMap (RingHom.id R) E F

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {σ : R ->+* S} {τ : S ->+* T} {E : Type*}
  [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F] {G : Type*}
  [AddCommGroup G] [Module T G]

namespace LinearPMap

open Submodule

/-- The (semi)linear map as just a function. -/
@[coe]
/--
Definition of `toFun'` / `toFun'` 的定义

English:
definition toFun'
  signature: (f : E ->ₛₗ.[σ] F)
  body: f.toFun

中文:
定义 toFun'
  签名: (f : E ->ₛₗ.[σ] F)
  定义体: f.toFun

Depends on / 依赖: f.toFun
-/
def toFun' (f : E ->ₛₗ.[σ] F) : f.domain -> F := f.toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (E ->ₛₗ.[σ] F) fun f
  body: ⟨toFun'⟩

@[simp]

中文:
实例 :
  签名: CoeFun (E ->ₛₗ.[σ] F) fun f
  定义体: ⟨toFun'⟩

@[simp]
-/
instance : CoeFun (E ->ₛₗ.[σ] F) fun f : E ->ₛₗ.[σ] F => f.domain -> F :=
  ⟨toFun'⟩

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : E ->ₛₗ.[σ] F) (x : f.domain)
  statement: f.toFun x = f x
  proof: rfl

@[ext (iff := false)]

中文:
定理 toFun_eq_coe
  条件: (f : E ->ₛₗ.[σ] F) (x : f.domain)
  结论: f.toFun x = f x
  证明: rfl

@[ext (iff := false)]
-/
theorem toFun_eq_coe (f : E ->ₛₗ.[σ] F) (x : f.domain) : f.toFun x = f x :=
  rfl

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
  proof: by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  congr
  apply LinearMap.ext
  intro x
  apply h'

中文:
定理 ext
  结论: {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
  证明: by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  congr
  apply LinearMap.ext
  intro x
  apply h'

Depends on / 依赖: LinearMap, LinearMap.ext, f_dom, g_dom
-/
theorem ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
    (h' : forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g := by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  congr
  apply LinearMap.ext
  intro x
  apply h'

/--
theorem `dExt` / 定理 `dExt`

English:
theorem dExt
  statement: {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
  proof: ext h fun _ _ _ => h' rfl

@[simp]

中文:
定理 dExt
  结论: {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
  证明: ext h fun _ _ _ => h' rfl

@[simp]
-/
theorem dExt {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain)
    (h' : forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g :=
  ext h fun _ _ _ => h' rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : E ->ₛₗ.[σ] F)
  statement: f 0 = 0
  proof: f.toFun.map_zero

中文:
定理 map_zero
  条件: (f : E ->ₛₗ.[σ] F)
  结论: f 0 = 0
  证明: f.toFun.map_zero

Depends on / 依赖: f.toFun.map_zero, map_zero
-/
theorem map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0 :=
  f.toFun.map_zero

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {f g : E ->ₛₗ.[σ] F}
  proof: ⟨by rintro rfl; simp, fun ⟨deq, feq⟩ => ext deq feq⟩

中文:
定理 ext_iff
  条件: {f g : E ->ₛₗ.[σ] F}
  证明: ⟨by rintro rfl; simp, fun ⟨deq, feq⟩ => ext deq feq⟩
-/
theorem ext_iff {f g : E ->ₛₗ.[σ] F} :
    f = g ↔
      f.domain = g.domain ∧
        forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩ :=
  ⟨by rintro rfl; simp, fun ⟨deq, feq⟩ => ext deq feq⟩

/--
theorem `dExt_iff` / 定理 `dExt_iff`

English:
theorem dExt_iff
  given: {f g : E ->ₛₗ.[σ] F}
  proof: ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => dExt deq feq⟩

中文:
定理 dExt_iff
  条件: {f g : E ->ₛₗ.[σ] F}
  证明: ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => dExt deq feq⟩

Depends on / 依赖: mod_cast
-/
theorem dExt_iff {f g : E ->ₛₗ.[σ] F} :
    f = g ↔
      exists _domain_eq : f.domain = g.domain,
        forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y :=
  ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => dExt deq feq⟩

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {s : Submodule R E} {f g : s ->ₛₗ[σ] F} (h : f = g)
  statement: mk s f = mk s g
  proof: h ▸ rfl

中文:
定理 ext'
  条件: {s : 子模 R E} {f g : s ->ₛₗ[σ] F} (h : f = g)
  结论: mk s f = mk s g
  证明: h ▸ rfl
-/
theorem ext' {s : Submodule R E} {f g : s ->ₛₗ[σ] F} (h : f = g) : mk s f = mk s g :=
  h ▸ rfl

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : E ->ₛₗ.[σ] F) (x y : f.domain)
  statement: f (x + y) = f x + f y
  proof: f.toFun.map_add x y

中文:
定理 map_add
  条件: (f : E ->ₛₗ.[σ] F) (x y : f.domain)
  结论: f (x + y) = f x + f y
  证明: f.toFun.map_add x y

Depends on / 依赖: f.toFun.map_add, map_add
-/
theorem map_add (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : E ->ₛₗ.[σ] F) (x : f.domain)
  statement: f (-x) = -f x
  proof: f.toFun.map_neg x

中文:
定理 map_neg
  条件: (f : E ->ₛₗ.[σ] F) (x : f.domain)
  结论: f (-x) = -f x
  证明: f.toFun.map_neg x

Depends on / 依赖: f.toFun.map_neg, map_neg
-/
theorem map_neg (f : E ->ₛₗ.[σ] F) (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : E ->ₛₗ.[σ] F) (x y : f.domain)
  statement: f (x - y) = f x - f y
  proof: f.toFun.map_sub x y

中文:
定理 map_sub
  条件: (f : E ->ₛₗ.[σ] F) (x y : f.domain)
  结论: f (x - y) = f x - f y
  证明: f.toFun.map_sub x y

Depends on / 依赖: f.toFun.map_sub, map_sub
-/
theorem map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [Module R F] (f : E ->ₗ.[R] F) (c : R) (x : f.domain)
  statement: f (c • x) = c • f x
  proof: f.toFun.map_smulₛₗ c x

中文:
定理 map_smul
  条件: [模 R F] (f : E ->ₗ.[R] F) (c : R) (x : f.domain)
  结论: f (c • x) = c • f x
  证明: f.toFun.map_smulₛₗ c x

Depends on / 依赖: f.toFun.map_smul
-/
theorem map_smul [Module R F] (f : E ->ₗ.[R] F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.toFun.map_smulₛₗ c x

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (f : E ->ₛₗ.[σ] F) (c : R) (x : f.domain)
  statement: f (c • x) = σ c • f x
  proof: f.toFun.map_smulₛₗ c x

@[simp]

中文:
定理 map_smulₛₗ
  条件: (f : E ->ₛₗ.[σ] F) (c : R) (x : f.domain)
  结论: f (c • x) = σ c • f x
  证明: f.toFun.map_smulₛₗ c x

@[simp]

Depends on / 依赖: f.toFun.map_smul
-/
theorem map_smulₛₗ (f : E ->ₛₗ.[σ] F) (c : R) (x : f.domain) : f (c • x) = σ c • f x :=
  f.toFun.map_smulₛₗ c x

@[simp]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (p : Submodule R E) (f : p ->ₛₗ[σ] F) (x : p)
  statement: mk p f x = f x
  proof: rfl

中文:
定理 mk_apply
  条件: (p : 子模 R E) (f : p ->ₛₗ[σ] F) (x : p)
  结论: mk p f x = f x
  证明: rfl
-/
theorem mk_apply (p : Submodule R E) (f : p ->ₛₗ[σ] F) (x : p) : mk p f x = f x := rfl

/--
Definition of `mkSpanSingleton'` / `mkSpanSingleton'` 的定义

English:
definition mkSpanSingleton'
  signature: (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0)
  body: R ∙ x
  toFun :=
    have H : forall c₁ c₂ : R, c₁ • x = c₂ • x -> σ c₁ • y = σ c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero]; rw [← sub_smul] at h ⊢
      rw [← RingHom.map_sub]
      exact H _ h
    { toFun z := σ (Classical.choose (mem_span_singleton.1 z.prop)) • y
      map_add' y' z

中文:
定义 mkSpanSingleton'
  签名: (x : E) (y : F) (H : 对任意 c : R, c • x = 0 -> σ c • y = 0)
  定义体: R ∙ x
  toFun :=
    have H : forall c₁ c₂ : R, c₁ • x = c₂ • x -> σ c₁ • y = σ c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero]; rw [← sub_smul] at h ⊢
      rw [← RingHom.map_sub]
      exact H _ h
    { toFun z := σ (Classical.choose (mem_span_singleton.1 z.prop)) • y
      map_add' y' z
-/
noncomputable def mkSpanSingleton' (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) :
    E ->ₛₗ.[σ] F where
  domain := R ∙ x
  toFun :=
    have H : forall c₁ c₂ : R, c₁ • x = c₂ • x -> σ c₁ • y = σ c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero]; rw [← sub_smul] at h ⊢
      rw [← RingHom.map_sub]
      exact H _ h
    { toFun z := σ (Classical.choose (mem_span_singleton.1 z.prop)) • y
      map_add' y' z' := by
        rw [← add_smul]; rw [← RingHom.map_add]; rw [H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [add_smul, this, ← coe_add]
      map_smul' c z := by
        rw [smul_smul]; rw [← RingHom.map_mul]; rw [H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [mul_smul, this]
        apply coe_smul }

@[simp]
/--
theorem `domain_mkSpanSingleton` / 定理 `domain_mkSpanSingleton`

English:
theorem domain_mkSpanSingleton
  given: (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0)
  proof: rfl

@[simp]

中文:
定理 domain_mkSpanSingleton
  条件: (x : E) (y : F) (H : 对任意 c : R, c • x = 0 -> σ c • y = 0)
  证明: rfl

@[simp]
-/
theorem domain_mkSpanSingleton (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) :
    (mkSpanSingleton' x y H).domain = R ∙ x :=
  rfl

@[simp]
/--
theorem `mkSpanSingleton'_apply` / 定理 `mkSpanSingleton'_apply`

English:
theorem mkSpanSingleton'_apply
  given: (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) (c : R) (h)
  proof: by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [← RingHom.map_sub]
  apply H
  simp only [sub_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)

@[simp]

中文:
定理 mkSpanSingleton'_apply
  条件: (x : E) (y : F) (H : 对任意 c : R, c • x = 0 -> σ c • y = 0) (c : R) (h)
  证明: by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [← RingHom.map_sub]
  apply H
  simp only [sub_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)

@[simp]
-/
theorem mkSpanSingleton'_apply (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) (c : R) (h) :
    mkSpanSingleton' x y H ⟨c • x, h⟩ = σ c • y := by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [← RingHom.map_sub]
  apply H
  simp only [sub_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)

@[simp]
/--
theorem `mkSpanSingleton'_apply_self` / 定理 `mkSpanSingleton'_apply_self`

English:
theorem mkSpanSingleton'_apply_self
  given: (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) (h)
  proof: by
  conv_rhs => rw [← one_smul S y]
  rw [← RingHom.map_one]; rw [← mkSpanSingleton'_apply x y H 1 ?_]
  · congr
    rw [one_smul]
  · rwa [one_smul]

中文:
定理 mkSpanSingleton'_apply_self
  条件: (x : E) (y : F) (H : 对任意 c : R, c • x = 0 -> σ c • y = 0) (h)
  证明: by
  conv_rhs => rw [← one_smul S y]
  rw [← RingHom.map_one]; rw [← mkSpanSingleton'_apply x y H 1 ?_]
  · congr
    rw [one_smul]
  · rwa [one_smul]
-/
theorem mkSpanSingleton'_apply_self (x : E) (y : F) (H : forall c : R, c • x = 0 -> σ c • y = 0) (h) :
    mkSpanSingleton' x y H ⟨x, h⟩ = y := by
  conv_rhs => rw [← one_smul S y]
  rw [← RingHom.map_one]; rw [← mkSpanSingleton'_apply x y H 1 ?_]
  · congr
    rw [one_smul]
  · rwa [one_smul]

/--
Definition of `mkSpanSingleton` / `mkSpanSingleton` 的定义

English:
abbreviation mkSpanSingleton
  signature: {K L E F : Type*} [DivisionRing K] [DivisionRing L]
  body: mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, RingHom.map_zero, zero_smul]) fun hx' =>
    absurd hx' hx

中文:
缩写 mkSpanSingleton
  签名: {K L E F : 类型} [除环 K] [除环 L]
  定义体: mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, RingHom.map_zero, zero_smul]) fun hx' =>
    absurd hx' hx

Depends on / 依赖: RingHom, RingHom.map_zero, absurd, map_zero, mkSpanSingleton, smul_eq_zero, zero_smul
-/
noncomputable abbrev mkSpanSingleton {K L E F : Type*} [DivisionRing K] [DivisionRing L]
    {σ : K ->+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module L F] (x : E) (y : F)
    (hx : x != 0) : E ->ₛₗ.[σ] F :=
  mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, RingHom.map_zero, zero_smul]) fun hx' =>
    absurd hx' hx

/--
theorem `mkSpanSingleton_apply` / 定理 `mkSpanSingleton_apply`

English:
theorem mkSpanSingleton_apply
  statement: (K L : Type*) {E F : Type*} [DivisionRing K] [DivisionRing L]
  proof: LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

中文:
定理 mkSpanSingleton_apply
  结论: (K L : 类型) {E F : 类型} [除环 K] [除环 L]
  证明: LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

Depends on / 依赖: LinearPMap, LinearPMap.mkSpanSingleton, _apply_self, mkSpanSingleton
-/
theorem mkSpanSingleton_apply (K L : Type*) {E F : Type*} [DivisionRing K] [DivisionRing L]
    {σ : K ->+* L} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module L F] {x : E} (hx : x != 0)
    (y : F) :
    (mkSpanSingleton x y hx : E ->ₛₗ.[σ] F)
      ⟨x, (Submodule.mem_span_singleton_self x : x in Submodule.span K {x})⟩ = y :=
  LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: [Module R F] (p : Submodule R E) (p' : Submodule R F)
  body: p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype

@[simp]

中文:
定义 fst
  签名: [模 R F] (p : 子模 R E) (p' : 子模 R F)
  定义体: p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype

@[simp]
-/
protected def fst [Module R F] (p : Submodule R E) (p' : Submodule R F) : E × F ->ₗ.[R] E where
  domain := p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype

@[simp]
/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p')
  proof: rfl

中文:
定理 fst_apply
  条件: [模 R F] (p : 子模 R E) (p' : 子模 R F) (x : p.乘积 p')
  证明: rfl
-/
theorem fst_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.fst p p' x = (x : E × F).1 :=
  rfl

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: [Module R F] (p : Submodule R E) (p' : Submodule R F)
  body: p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype

@[simp]

中文:
定义 snd
  签名: [模 R F] (p : 子模 R E) (p' : 子模 R F)
  定义体: p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype

@[simp]
-/
protected def snd [Module R F] (p : Submodule R E) (p' : Submodule R F) : E × F ->ₗ.[R] F where
  domain := p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype

@[simp]
/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p')
  proof: rfl

中文:
定理 snd_apply
  条件: [模 R F] (p : 子模 R E) (p' : 子模 R F) (x : p.乘积 p')
  证明: rfl
-/
theorem snd_apply [Module R F] (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.snd p p' x = (x : E × F).2 :=
  rfl

/--
Instance `le` / 实例 `le`

English:
instance le
  signature: : LE (E ->ₛₗ.[σ] F)
  body: ⟨fun f g => f.domain <= g.domain ∧ forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩

中文:
实例 le
  签名: : LE (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g => f.domain <= g.domain ∧ forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩

Depends on / 依赖: domain, f.domain, g.domain
-/
instance le : LE (E ->ₛₗ.[σ] F) :=
  ⟨fun f g => f.domain <= g.domain ∧ forall ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩

/--
theorem `apply_comp_inclusion` / 定理 `apply_comp_inclusion`

English:
theorem apply_comp_inclusion
  given: {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain)
  proof: h.2 rfl

中文:
定理 apply_comp_inclusion
  条件: {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain)
  证明: h.2 rfl
-/
theorem apply_comp_inclusion {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain) :
    T x = S (Submodule.inclusion h.1 x) :=
  h.2 rfl

/--
theorem `exists_of_le` / 定理 `exists_of_le`

English:
theorem exists_of_le
  given: {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain)
  proof: ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩

中文:
定理 存在_of_le
  条件: {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain)
  证明: ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩
-/
theorem exists_of_le {T S : E ->ₛₗ.[σ] F} (h : T <= S) (x : T.domain) :
    exists y : S.domain, (x : E) = y ∧ T x = S y :=
  ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩

/--
theorem `eq_of_le_of_domain_eq` / 定理 `eq_of_le_of_domain_eq`

English:
theorem eq_of_le_of_domain_eq
  given: {f g : E ->ₛₗ.[σ] F} (hle : f <= g) (heq : f.domain = g.domain)
  proof: dExt heq hle.2

中文:
定理 eq_of_le_of_domain_eq
  条件: {f g : E ->ₛₗ.[σ] F} (hle : f <= g) (heq : f.domain = g.domain)
  证明: dExt heq hle.2
-/
theorem eq_of_le_of_domain_eq {f g : E ->ₛₗ.[σ] F} (hle : f <= g) (heq : f.domain = g.domain) :
    f = g :=
  dExt heq hle.2

/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : E ->ₛₗ.[σ] F)
  body: { x | exists (hf : x in f.domain) (hg : x in g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' {x y} := fun ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      simp_all [← AddMemClass.mk_add_mk, f.map_

中文:
定义 eqLocus
  签名: (f g : E ->ₛₗ.[σ] F)
  定义体: { x | exists (hf : x in f.domain) (hg : x in g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' {x y} := fun ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      simp_all [← AddMemClass.mk_add_mk, f.map_

Depends on / 依赖: domain, f.domain, g.domain
-/
def eqLocus (f g : E ->ₛₗ.[σ] F) : Submodule R E where
  carrier := { x | exists (hf : x in f.domain) (hg : x in g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' {x y} := fun ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      simp_all [← AddMemClass.mk_add_mk, f.map_add, g.map_add]⟩
  smul_mem' c x := fun ⟨hfx, hgx, hx⟩ =>
    ⟨smul_mem _ c hfx, smul_mem _ c hgx, by
      have {f : E ->ₛₗ.[σ] F} (hfx) : (⟨c • x, smul_mem _ c hfx⟩ : f.domain) = c • ⟨x, hfx⟩ := by
        simp
      rw [this hfx]; rw [this hgx]; rw [f.map_smulₛₗ]; rw [g.map_smulₛₗ]; rw [hx]⟩

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : Bot (E ->ₛₗ.[σ] F)
  body: ⟨⟨⊥, 0⟩⟩

中文:
实例 bot
  签名: : 底元素 (E ->ₛₗ.[σ] F)
  定义体: ⟨⟨⊥, 0⟩⟩
-/
instance bot : Bot (E ->ₛₗ.[σ] F) :=
  ⟨⟨⊥, 0⟩⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (E ->ₛₗ.[σ] F)
  body: ⟨⊥⟩

中文:
实例 inhabited
  签名: : 可居 (E ->ₛₗ.[σ] F)
  定义体: ⟨⊥⟩
-/
instance inhabited : Inhabited (E ->ₛₗ.[σ] F) :=
  ⟨⊥⟩

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: : SemilatticeInf (E ->ₛₗ.[σ] F) where
  body: ⟨le_refl f.domain, fun _ _ h => Subtype.ext h ▸ rfl⟩
  le_trans := fun _ _ _ ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x _ hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm _ _ fg gf := eq_of_le_of_do

中文:
实例 semilatticeInf
  签名: : SemilatticeInf (E ->ₛₗ.[σ] F) where
  定义体: ⟨le_refl f.domain, fun _ _ h => Subtype.ext h ▸ rfl⟩
  le_trans := fun _ _ _ ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x _ hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm _ _ fg gf := eq_of_le_of_do

Depends on / 依赖: Subtype, Subtype.ext, domain, f.domain, le_refl
-/
instance semilatticeInf : SemilatticeInf (E ->ₛₗ.[σ] F) where
  le_refl f := ⟨le_refl f.domain, fun _ _ h => Subtype.ext h ▸ rfl⟩
  le_trans := fun _ _ _ ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x _ hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm _ _ fg gf := eq_of_le_of_domain_eq fg (le_antisymm fg.1 gf.1)
inf f g := ⟨f.eqLocus g, f.toFun.comp inclusion fun _x hx => hx.fst⟩
  le_inf := by
    intro f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩
    exact ⟨fun x hx =>
      ⟨fg_le hx, fh_le hx,
      (fg_eq (x := ⟨x, hx⟩) rfl).symm.trans (fh_eq rfl)⟩,
      fun x ⟨y, yg, hy⟩ h => fg_eq h⟩
inf_le_left f _ := ⟨fun _ hx => hx.fst, fun _ _ h => congr_arg f Subtype.ext h⟩
  inf_le_right _ g :=
⟨fun _ hx => hx.snd.fst, fun ⟨_, _, _, hx⟩ _ h => hx.trans congr_arg g Subtype.ext h⟩

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (E ->ₛₗ.[σ] F) where
  body: ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.ext ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.ext (h.symm.trans (congr_arg _ hx))
      rw [hx]; rw [hy]; rw [map_zero]; rw [map_zero]⟩

中文:
实例 orderBot
  签名: : 有底序 (E ->ₛₗ.[σ] F) where
  定义体: ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.ext ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.ext (h.symm.trans (congr_arg _ hx))
      rw [hx]; rw [hy]; rw [map_zero]; rw [map_zero]⟩

Depends on / 依赖: Subtype, Subtype.ext, bot_le, congr_arg, h.symm.trans, map_zero, mem_bot
-/
instance orderBot : OrderBot (E ->ₛₗ.[σ] F) where
  bot_le f :=
    ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.ext ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.ext (h.symm.trans (congr_arg _ hx))
      rw [hx]; rw [hy]; rw [map_zero]; rw [map_zero]⟩

/--
theorem `le_of_eqLocus_ge` / 定理 `le_of_eqLocus_ge`

English:
theorem le_of_eqLocus_ge
  given: {f g : E ->ₛₗ.[σ] F} (H : f.domain <= f.eqLocus g)
  statement: f <= g
  proof: suffices f <= f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g <= f).2 hxy.symm).symm⟩

中文:
定理 le_of_eqLocus_ge
  条件: {f g : E ->ₛₗ.[σ] F} (H : f.domain <= f.eqLocus g)
  结论: f <= g
  证明: suffices f <= f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g <= f).2 hxy.symm).symm⟩

Depends on / 依赖: hxy.symm, inf_le_left, inf_le_right, le_trans
-/
theorem le_of_eqLocus_ge {f g : E ->ₛₗ.[σ] F} (H : f.domain <= f.eqLocus g) : f <= g :=
  suffices f <= f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g <= f).2 hxy.symm).symm⟩

/--
theorem `domain_mono` / 定理 `domain_mono`

English:
theorem domain_mono
  statement: StrictMono (domain (σ := σ) (E := E) (F := F))
  proof: fun _f _g hlt =>
lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt eq_of_le_of_domain_eq (le_of_lt hlt) heq

中文:
定理 domain_mono
  结论: 严格递增 (domain (σ := σ) (E := E) (F := F))
  证明: fun _f _g hlt =>
lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt eq_of_le_of_domain_eq (le_of_lt hlt) heq
-/
theorem domain_mono : StrictMono (domain (σ := σ) (E := E) (F := F)) :=
  fun _f _g hlt =>
lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt eq_of_le_of_domain_eq (le_of_lt hlt) heq

set_option backward.privateInPublic true in
/--
theorem `sup_aux` / 定理 `sup_aux`

English:
theorem sup_aux
  statement: (f g : E ->ₛₗ.[σ] F)
  proof: by
  choose x hx y hy hxy using fun z : ↥(f.domain ⊔ g.domain) => mem_sup.1 z.prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq : forall (x' : f.domain) (y' : g.domain) (z' : ↥(f.domain ⊔ g.domain))
      (_H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
  

中文:
定理 sup_aux
  结论: (f g : E ->ₛₗ.[σ] F)
  证明: by
  choose x hx y hy hxy using fun z : ↥(f.domain ⊔ g.domain) => mem_sup.1 z.prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq : forall (x' : f.domain) (y' : g.domain) (z' : ↥(f.domain ⊔ g.domain))
      (_H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
  
-/
private theorem sup_aux (f g : E ->ₛₗ.[σ] F)
    (h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) :
    exists fg : ↥(f.domain ⊔ g.domain) ->ₛₗ[σ] F,
      forall (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)),
        (x : E) + y = ↑z -> fg z = f x + g y := by
  choose x hx y hy hxy using fun z : ↥(f.domain ⊔ g.domain) => mem_sup.1 z.prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq : forall (x' : f.domain) (y' : g.domain) (z' : ↥(f.domain ⊔ g.domain))
      (_H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
    dsimp [fg]
    rw [add_comm]; rw [← sub_eq_sub_iff_add_eq_add]; rw [eq_comm]; rw [← map_sub]; rw [← map_sub]
    apply h
    simp only [← eq_sub_iff_add_eq] at hxy
    simp only [AddSubgroupClass.coe_sub, hxy, ← sub_add, ← sub_sub, sub_self,
      zero_sub, ← H]
    apply neg_add_eq_sub
  use { toFun := fg, map_add' := ?_, map_smul' := ?_ }, fg_eq
  · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    rw [← add_assoc]; rw [add_right_comm (f _)]; rw [← map_add]; rw [add_assoc]; rw [← map_add]
    apply fg_eq
    simp only [coe_add, ← add_assoc]
    rw [add_right_comm (x _)]; rw [hxy]; rw [add_assoc]; rw [hxy]; rw [coe_mk]; rw [coe_mk]
  · intro c z
    rw [smul_add]; rw [← map_smulₛₗ]; rw [← map_smulₛₗ]
    apply fg_eq
    simp only [coe_smul, ← smul_add, hxy]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def sup (f g : E ->ₛₗ.[σ] F)
  body: ⟨_, Classical.choose (sup_aux f g h)⟩

@[simp]

中文:
定义 noncomputable
  签名: def 上确界 (f g : E ->ₛₗ.[σ] F)
  定义体: ⟨_, Classical.choose (sup_aux f g h)⟩

@[simp]
-/
protected noncomputable def sup (f g : E ->ₛₗ.[σ] F)
    (h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) : E ->ₛₗ.[σ] F :=
  ⟨_, Classical.choose (sup_aux f g h)⟩

@[simp]
/--
theorem `domain_sup` / 定理 `domain_sup`

English:
theorem domain_sup
  statement: (f g : E ->ₛₗ.[σ] F)
  proof: rfl

中文:
定理 domain_sup
  结论: (f g : E ->ₛₗ.[σ] F)
  证明: rfl
-/
theorem domain_sup (f g : E ->ₛₗ.[σ] F)
    (h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) :
    (f.sup g h).domain = f.domain ⊔ g.domain :=
  rfl

/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  statement: {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y)
  proof: Classical.choose_spec (sup_aux f g H) x y z hz

中文:
定理 sup_apply
  结论: {f g : E ->ₛₗ.[σ] F} (H : 对任意 (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y)
  证明: Classical.choose_spec (sup_aux f g H) x y z hz

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, sup_aux
-/
theorem sup_apply {f g : E ->ₛₗ.[σ] F} (H : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y)
    (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)) (hz : (↑x : E) + ↑y = ↑z) :
    f.sup g H z = f x + g y :=
  Classical.choose_spec (sup_aux f g H) x y z hz

/--
theorem `left_le_sup` / 定理 `left_le_sup`

English:
theorem left_le_sup
  statement: (f g : E ->ₛₗ.[σ] F)
  proof: by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _)]; rw [← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

中文:
定理 left_le_sup
  结论: (f g : E ->ₛₗ.[σ] F)
  证明: by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _)]; rw [← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
-/
protected theorem left_le_sup (f g : E ->ₛₗ.[σ] F)
    (h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) : f <= f.sup g h := by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _)]; rw [← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

/--
theorem `right_le_sup` / 定理 `right_le_sup`

English:
theorem right_le_sup
  statement: (f g : E ->ₛₗ.[σ] F)
  proof: by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _)]; rw [← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

中文:
定理 right_le_sup
  结论: (f g : E ->ₛₗ.[σ] F)
  证明: by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _)]; rw [← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
-/
protected theorem right_le_sup (f g : E ->ₛₗ.[σ] F)
    (h : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) : g <= f.sup g h := by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _)]; rw [← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  statement: {f g h : E ->ₛₗ.[σ] F}
  proof: have Hf : f <= f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g <= f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
le_of_eqLocus_ge sup_le Hf.1 Hg.1

中文:
定理 sup_le
  结论: {f g h : E ->ₛₗ.[σ] F}
  证明: have Hf : f <= f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g <= f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
le_of_eqLocus_ge sup_le Hf.1 Hg.1
-/
protected theorem sup_le {f g h : E ->ₛₗ.[σ] F}
    (H : forall (x : f.domain) (y : g.domain), (x : E) = y -> f x = g y) (fh : f <= h) (gh : g <= h) :
    f.sup g H <= h :=
  have Hf : f <= f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g <= f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
le_of_eqLocus_ge sup_le Hf.1 Hg.1

/--
theorem `sup_h_of_disjoint` / 定理 `sup_h_of_disjoint`

English:
theorem sup_h_of_disjoint
  statement: (f g : E ->ₛₗ.[σ] F) (h : Disjoint f.domain g.domain) (x : f.domain)
  proof: by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.ext (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.ext (hxy.trans <| congr_arg _ hy)
  simp [*]

中文:
定理 sup_h_of_disjoint
  结论: (f g : E ->ₛₗ.[σ] F) (h : Disjoint f.domain g.domain) (x : f.domain)
  证明: by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.ext (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.ext (hxy.trans <| congr_arg _ hy)
  simp [*]

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, disjoint_def, hxy.trans
-/
theorem sup_h_of_disjoint (f g : E ->ₛₗ.[σ] F) (h : Disjoint f.domain g.domain) (x : f.domain)
    (y : g.domain) (hxy : (x : E) = y) : f x = g y := by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.ext (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.ext (hxy.trans <| congr_arg _ hy)
  simp [*]

/-! ### Algebraic operations -/


section Zero

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (E ->ₛₗ.[σ] F)
  body: ⟨⊤, 0⟩

@[simp]

中文:
实例 instZero
  签名: : 零 (E ->ₛₗ.[σ] F)
  定义体: ⟨⊤, 0⟩

@[simp]
-/
instance instZero : Zero (E ->ₛₗ.[σ] F) := ⟨⊤, 0⟩

@[simp]
/--
theorem `zero_domain` / 定理 `zero_domain`

English:
theorem zero_domain
  statement: (0 : E ->ₛₗ.[σ] F).domain = ⊤
  proof: rfl

@[simp]

中文:
定理 zero_domain
  结论: (0 : E ->ₛₗ.[σ] F).domain = ⊤
  证明: rfl

@[simp]
-/
theorem zero_domain : (0 : E ->ₛₗ.[σ] F).domain = ⊤ := rfl

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : (⊤ : Submodule R E))
  statement: (0 : E ->ₛₗ.[σ] F) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (x : (⊤ : 子模 R E))
  结论: (0 : E ->ₛₗ.[σ] F) x = 0
  证明: rfl
-/
theorem zero_apply (x : (⊤ : Submodule R E)) : (0 : E ->ₛₗ.[σ] F) x = 0 := rfl

end Zero

section SMul

variable {M N : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass S M F]
variable [Monoid N] [DistribMulAction N F] [SMulCommClass S N F]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul M (E ->ₛₗ.[σ] F)
  body: ⟨fun a f =>
    { domain := f.domain
      toFun := a • f.toFun }⟩

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 M (E ->ₛₗ.[σ] F)
  定义体: ⟨fun a f =>
    { domain := f.domain
      toFun := a • f.toFun }⟩

@[simp]

Depends on / 依赖: domain, f.domain, f.toFun
-/
instance instSMul : SMul M (E ->ₛₗ.[σ] F) :=
  ⟨fun a f =>
    { domain := f.domain
      toFun := a • f.toFun }⟩

@[simp]
/--
theorem `smul_domain` / 定理 `smul_domain`

English:
theorem smul_domain
  given: (a : M) (f : E ->ₛₗ.[σ] F)
  statement: (a • f).domain = f.domain
  proof: rfl

中文:
定理 smul_domain
  条件: (a : M) (f : E ->ₛₗ.[σ] F)
  结论: (a • f).domain = f.domain
  证明: rfl
-/
theorem smul_domain (a : M) (f : E ->ₛₗ.[σ] F) : (a • f).domain = f.domain :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (a : M) (f : E ->ₛₗ.[σ] F) (x : (a • f).domain)
  statement: (a • f) x = a • f x
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: (a : M) (f : E ->ₛₗ.[σ] F) (x : (a • f).domain)
  结论: (a • f) x = a • f x
  证明: rfl

@[simp]
-/
theorem smul_apply (a : M) (f : E ->ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a • f x :=
  rfl

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (a : M) (f : E ->ₛₗ.[σ] F)
  statement: ⇑(a • f) = a • ⇑f
  proof: rfl

中文:
定理 coe_smul
  条件: (a : M) (f : E ->ₛₗ.[σ] F)
  结论: ⇑(a • f) = a • ⇑f
  证明: rfl
-/
theorem coe_smul (a : M) (f : E ->ₛₗ.[σ] F) : ⇑(a • f) = a • ⇑f :=
  rfl

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass M N F]
  body: ⟨fun a b f => ext' smul_comm a b f.toFun⟩

中文:
实例 instSMulCommClass
  签名: [标量交换类 M N F]
  定义体: ⟨fun a b f => ext' smul_comm a b f.toFun⟩

Depends on / 依赖: f.toFun, smul_comm
-/
instance instSMulCommClass [SMulCommClass M N F] : SMulCommClass M N (E ->ₛₗ.[σ] F) :=
⟨fun a b f => ext' smul_comm a b f.toFun⟩

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul M N] [IsScalarTower M N F]
  body: ⟨fun a b f => ext' smul_assoc a b f.toFun⟩

中文:
实例 instIsScalarTower
  签名: [标量乘法 M N] [标量塔 M N F]
  定义体: ⟨fun a b f => ext' smul_assoc a b f.toFun⟩

Depends on / 依赖: f.toFun, smul_assoc
-/
instance instIsScalarTower [SMul M N] [IsScalarTower M N F] : IsScalarTower M N (E ->ₛₗ.[σ] F) :=
⟨fun a b f => ext' smul_assoc a b f.toFun⟩

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: : MulAction M (E ->ₛₗ.[σ] F) where
  body: fun ⟨_s, f⟩ => ext' one_smul M f
mul_smul a b f := ext' mul_smul a b f.toFun

中文:
实例 instMulAction
  签名: : 乘法作用 M (E ->ₛₗ.[σ] F) where
  定义体: fun ⟨_s, f⟩ => ext' one_smul M f
mul_smul a b f := ext' mul_smul a b f.toFun

Depends on / 依赖: one_smul
-/
instance instMulAction : MulAction M (E ->ₛₗ.[σ] F) where
one_smul := fun ⟨_s, f⟩ => ext' one_smul M f
mul_smul a b f := ext' mul_smul a b f.toFun

end SMul

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (E ->ₛₗ.[σ] F)
  body: ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]

Depends on / 依赖: domain, f.domain, f.toFun
-/
instance instNeg : Neg (E ->ₛₗ.[σ] F) :=
  ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]
/--
theorem `neg_domain` / 定理 `neg_domain`

English:
theorem neg_domain
  given: (f : E ->ₛₗ.[σ] F)
  statement: (-f).domain = f.domain
  proof: rfl

@[simp]

中文:
定理 neg_domain
  条件: (f : E ->ₛₗ.[σ] F)
  结论: (-f).domain = f.domain
  证明: rfl

@[simp]
-/
theorem neg_domain (f : E ->ₛₗ.[σ] F) : (-f).domain = f.domain := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : E ->ₛₗ.[σ] F) (x)
  statement: (-f) x = -f x
  proof: rfl

中文:
定理 neg_apply
  条件: (f : E ->ₛₗ.[σ] F) (x)
  结论: (-f) x = -f x
  证明: rfl
-/
theorem neg_apply (f : E ->ₛₗ.[σ] F) (x) : (-f) x = -f x :=
  rfl

/--
Instance `instInvolutiveNeg` / 实例 `instInvolutiveNeg`

English:
instance instInvolutiveNeg
  signature: : InvolutiveNeg (E ->ₛₗ.[σ] F)
  body: ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]⟩

中文:
实例 instInvolutiveNeg
  签名: : InvolutiveNeg (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]⟩

Depends on / 依赖: neg_apply, neg_neg
-/
instance instInvolutiveNeg : InvolutiveNeg (E ->ₛₗ.[σ] F) :=
  ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]⟩

section Add

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (E ->ₛₗ.[σ] F)
  body: ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        + g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

中文:
实例 instAdd
  签名: : 加法 (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        + g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

Depends on / 依赖: domain, f.domain, f.toFun.comp, g.domain, g.toFun.comp, inclusion, inf_le_left, inf_le_right
-/
instance instAdd : Add (E ->ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        + g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

/--
theorem `add_domain` / 定理 `add_domain`

English:
theorem add_domain
  given: (f g : E ->ₛₗ.[σ] F)
  statement: (f + g).domain = f.domain ⊓ g.domain
  proof: rfl

中文:
定理 add_domain
  条件: (f g : E ->ₛₗ.[σ] F)
  结论: (f + g).domain = f.domain ⊓ g.domain
  证明: rfl
-/
theorem add_domain (f g : E ->ₛₗ.[σ] F) : (f + g).domain = f.domain ⊓ g.domain := rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E))
  proof: rfl

中文:
定理 add_apply
  条件: (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : 子模 R E))
  证明: rfl
-/
theorem add_apply (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f + g) x = f ⟨x, x.prop.1⟩ + g ⟨x, x.prop.2⟩ := rfl

/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: : AddSemigroup (E ->ₛₗ.[σ] F)
  body: ⟨fun f g h => by
    ext x y hxy
    · simp only [add_domain, inf_assoc]
    · simp only [add_apply, add_assoc]⟩

中文:
实例 instAddSemigroup
  签名: : 加法半群 (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g h => by
    ext x y hxy
    · simp only [add_domain, inf_assoc]
    · simp only [add_apply, add_assoc]⟩

Depends on / 依赖: add_apply, add_assoc, add_domain, inf_assoc
-/
instance instAddSemigroup : AddSemigroup (E ->ₛₗ.[σ] F) :=
  ⟨fun f g h => by
    ext x y hxy
    · simp only [add_domain, inf_assoc]
    · simp only [add_apply, add_assoc]⟩

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: : AddZeroClass (E ->ₛₗ.[σ] F) where
  body: fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
  add_zero := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]

中文:
实例 instAddZeroClass
  签名: : 加法零类 (E ->ₛₗ.[σ] F) where
  定义体: fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
  add_zero := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]

Depends on / 依赖: add_apply, add_domain, add_zero
-/
instance instAddZeroClass : AddZeroClass (E ->ₛₗ.[σ] F) where
  zero_add := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
  add_zero := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid (E ->ₛₗ.[σ] F) where
  body: by
    simp
  add_zero := by
    simp
  nsmul := nsmulRec

中文:
实例 instAddMonoid
  签名: : 加法幺半群 (E ->ₛₗ.[σ] F) where
  定义体: by
    simp
  add_zero := by
    simp
  nsmul := nsmulRec

Depends on / 依赖: add_zero, nsmulRec
-/
instance instAddMonoid : AddMonoid (E ->ₛₗ.[σ] F) where
  zero_add f := by
    simp
  add_zero := by
    simp
  nsmul := nsmulRec

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (E ->ₛₗ.[σ] F)
  body: ⟨fun f g => by
    ext x y hxy
    · simp only [add_domain, inf_comm]
    · simp only [add_apply, add_comm]⟩

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g => by
    ext x y hxy
    · simp only [add_domain, inf_comm]
    · simp only [add_apply, add_comm]⟩

Depends on / 依赖: add_apply, add_comm, add_domain, inf_comm
-/
instance instAddCommMonoid : AddCommMonoid (E ->ₛₗ.[σ] F) :=
  ⟨fun f g => by
    ext x y hxy
    · simp only [add_domain, inf_comm]
    · simp only [add_apply, add_comm]⟩

end Add

section VAdd

/--
Instance `instVAdd` / 实例 `instVAdd`

English:
instance instVAdd
  signature: : VAdd (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F)
  body: ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩

@[simp]

中文:
实例 instVAdd
  签名: : 向量加法 (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩

@[simp]

Depends on / 依赖: domain, f.comp, g.domain, g.domain.subtype, g.toFun, subtype
-/
instance instVAdd : VAdd (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩

@[simp]
/--
theorem `vadd_domain` / 定理 `vadd_domain`

English:
theorem vadd_domain
  given: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F)
  statement: (f +ᵥ g).domain = g.domain
  proof: rfl

中文:
定理 vadd_domain
  条件: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F)
  结论: (f +ᵥ g).domain = g.domain
  证明: rfl
-/
theorem vadd_domain (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) : (f +ᵥ g).domain = g.domain :=
  rfl

/--
theorem `vadd_apply` / 定理 `vadd_apply`

English:
theorem vadd_apply
  given: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) (x : (f +ᵥ g).domain)
  proof: rfl

@[simp]

中文:
定理 vadd_apply
  条件: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) (x : (f +ᵥ g).domain)
  证明: rfl

@[simp]
-/
theorem vadd_apply (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) (x : (f +ᵥ g).domain) :
    (f +ᵥ g) x = f x + g x :=
  rfl

@[simp]
/--
theorem `coe_vadd` / 定理 `coe_vadd`

English:
theorem coe_vadd
  given: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F)
  statement: ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g
  proof: rfl

中文:
定理 coe_vadd
  条件: (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F)
  结论: ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g
  证明: rfl
-/
theorem coe_vadd (f : E ->ₛₗ[σ] F) (g : E ->ₛₗ.[σ] F) : ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g :=
  rfl

/--
Instance `instAddAction` / 实例 `instAddAction`

English:
instance instAddAction
  signature: : AddAction (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F) where
  body: (· +ᵥ ·)
zero_vadd := fun ⟨_s, _f⟩ => ext' zero_add _
add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' LinearMap.ext fun _x => add_assoc _ _ _

中文:
实例 instAddAction
  签名: : 加法作用 (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F) where
  定义体: (· +ᵥ ·)
zero_vadd := fun ⟨_s, _f⟩ => ext' zero_add _
add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' LinearMap.ext fun _x => add_assoc _ _ _
-/
instance instAddAction : AddAction (E ->ₛₗ[σ] F) (E ->ₛₗ.[σ] F) where
  vadd := (· +ᵥ ·)
zero_vadd := fun ⟨_s, _f⟩ => ext' zero_add _
add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' LinearMap.ext fun _x => add_assoc _ _ _

end VAdd

section Sub

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (E ->ₛₗ.[σ] F)
  body: ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        - g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

中文:
实例 instSub
  签名: : 减法 (E ->ₛₗ.[σ] F)
  定义体: ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        - g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

Depends on / 依赖: domain, f.domain, f.toFun.comp, g.domain, g.toFun.comp, inclusion, inf_le_left, inf_le_right
-/
instance instSub : Sub (E ->ₛₗ.[σ] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain <= _))
        - g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain <= _)) }⟩

/--
theorem `sub_domain` / 定理 `sub_domain`

English:
theorem sub_domain
  given: (f g : E ->ₛₗ.[σ] F)
  statement: (f - g).domain = f.domain ⊓ g.domain
  proof: rfl

中文:
定理 sub_domain
  条件: (f g : E ->ₛₗ.[σ] F)
  结论: (f - g).domain = f.domain ⊓ g.domain
  证明: rfl
-/
theorem sub_domain (f g : E ->ₛₗ.[σ] F) : (f - g).domain = f.domain ⊓ g.domain := rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E))
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : 子模 R E))
  证明: rfl
-/
theorem sub_apply (f g : E ->ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f - g) x = f ⟨x, x.prop.1⟩ - g ⟨x, x.prop.2⟩ := rfl

/--
Instance `instSubtractionCommMonoid` / 实例 `instSubtractionCommMonoid`

English:
instance instSubtractionCommMonoid
  signature: : SubtractionCommMonoid (E ->ₛₗ.[σ] F) where
  body: add_comm
  sub_eq_add_neg f g := by
    ext x _ h
    · rfl
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg]
  neg_neg := neg_neg
  neg_add_rev f g := by
    ext x _ h
    · simp [add_domain, neg_domain, And.comm]
    simp [add_apply, neg_apply, ← sub_eq_add_neg]
  neg_eq_of_add f g h' :

中文:
实例 instSubtractionCommMonoid
  签名: : SubtractionComm幺半群 (E ->ₛₗ.[σ] F) where
  定义体: add_comm
  sub_eq_add_neg f g := by
    ext x _ h
    · rfl
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg]
  neg_neg := neg_neg
  neg_add_rev f g := by
    ext x _ h
    · simp [add_domain, neg_domain, And.comm]
    simp [add_apply, neg_apply, ← sub_eq_add_neg]
  neg_eq_of_add f g h' :

Depends on / 依赖: add_comm
-/
instance instSubtractionCommMonoid : SubtractionCommMonoid (E ->ₛₗ.[σ] F) where
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
    · have : (0 : E ->ₛₗ.[σ] F).domain = ⊤ := zero_domain
      simp only [← h', add_domain, inf_eq_top_iff] at this
      rw [neg_domain]; rw [this.1]; rw [this.2]
    simp only [neg_domain, neg_apply, neg_eq_iff_add_eq_zero]
    rw [ext_iff] at h'
    rcases h' with ⟨hdom, h'⟩
    rw [zero_domain] at hdom
    simp only [hdom, zero_domain, mem_top, zero_apply, forall_true_left] at h'
    apply h'
  zsmul := zsmulRec

end Sub

section

variable {K L : Type*} [DivisionRing K] [DivisionRing L] {σ : K ->+* L} [Module K E] [Module L F]

/--
Definition of `supSpanSingleton` / `supSpanSingleton` 的定义

English:
definition supSpanSingleton
  signature: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain)
  body: f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem)
sup_h_of_disjoint _ _ by simpa [disjoint_span_singleton] using fun h => False.elim hx h

@[simp]

中文:
定义 supSpanSingleton
  签名: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain)
  定义体: f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem)
sup_h_of_disjoint _ _ by simpa [disjoint_span_singleton] using fun h => False.elim hx h

@[simp]

Depends on / 依赖: False.elim, disjoint_span_singleton, domain, f.domain.zero_mem, f.sup, mkSpanSingleton, sup_h_of_disjoint, zero_mem
-/
noncomputable def supSpanSingleton (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    E ->ₛₗ.[σ] F :=
f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem)
sup_h_of_disjoint _ _ by simpa [disjoint_span_singleton] using fun h => False.elim hx h

@[simp]
/--
theorem `domain_supSpanSingleton` / 定理 `domain_supSpanSingleton`

English:
theorem domain_supSpanSingleton
  given: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain)
  proof: rfl

中文:
定理 domain_supSpanSingleton
  条件: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain)
  证明: rfl
-/
theorem domain_supSpanSingleton (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    (f.supSpanSingleton x y hx).domain = f.domain ⊔ K ∙ x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `supSpanSingleton_apply_mk` / 定理 `supSpanSingleton_apply_mk`

English:
theorem supSpanSingleton_apply_mk
  statement: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
  proof: by
  unfold supSpanSingleton
  rw [sup_apply _ ⟨x']; rw [hx'⟩ ⟨c • x]; rw [_⟩]; rw [mkSpanSingleton'_apply]
  · rfl
  · exact mem_span_singleton.2 ⟨c, rfl⟩

@[simp]

中文:
定理 supSpanSingleton_apply_mk
  结论: (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
  证明: by
  unfold supSpanSingleton
  rw [sup_apply _ ⟨x']; rw [hx'⟩ ⟨c • x]; rw [_⟩]; rw [mkSpanSingleton'_apply]
  · rfl
  · exact mem_span_singleton.2 ⟨c, rfl⟩

@[simp]

Depends on / 依赖: _apply, mem_span_singleton, mkSpanSingleton, supSpanSingleton, sup_apply
-/
theorem supSpanSingleton_apply_mk (f : E ->ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
    (hx' : x' in f.domain) (c : K) :
    f.supSpanSingleton x y hx
        ⟨x' + c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
      f ⟨x', hx'⟩ + σ c • y := by
  unfold supSpanSingleton
  rw [sup_apply _ ⟨x']; rw [hx'⟩ ⟨c • x]; rw [_⟩]; rw [mkSpanSingleton'_apply]
  · rfl
  · exact mem_span_singleton.2 ⟨c, rfl⟩

@[simp]
/--
theorem `supSpanSingleton_apply_smul_self` / 定理 `supSpanSingleton_apply_smul_self`

English:
theorem supSpanSingleton_apply_smul_self
  statement: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  proof: by
  simpa [(mk_eq_zero _ _).mpr rfl] using supSpanSingleton_apply_mk f x y hx 0 (zero_mem _) c

@[simp]

中文:
定理 supSpanSingleton_apply_smul_self
  结论: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  证明: by
  simpa [(mk_eq_zero _ _).mpr rfl] using supSpanSingleton_apply_mk f x y hx 0 (zero_mem _) c

@[simp]

Depends on / 依赖: mk_eq_zero, supSpanSingleton_apply_mk, zero_mem
-/
theorem supSpanSingleton_apply_smul_self (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (c : K) :
f.supSpanSingleton x y hx ⟨c • x, mem_sup_right mem_span_singleton.2 ⟨c, rfl⟩⟩ =
      σ c • y := by
  simpa [(mk_eq_zero _ _).mpr rfl] using supSpanSingleton_apply_mk f x y hx 0 (zero_mem _) c

@[simp]
/--
theorem `supSpanSingleton_apply_self` / 定理 `supSpanSingleton_apply_self`

English:
theorem supSpanSingleton_apply_self
  given: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  proof: by
  simpa using supSpanSingleton_apply_smul_self f y hx 1

中文:
定理 supSpanSingleton_apply_self
  条件: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  证明: by
  simpa using supSpanSingleton_apply_smul_self f y hx 1

Depends on / 依赖: supSpanSingleton_apply_smul_self
-/
theorem supSpanSingleton_apply_self (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) :
f.supSpanSingleton x y hx ⟨x, mem_sup_right mem_span_singleton_self _⟩ = y := by
  simpa using supSpanSingleton_apply_smul_self f y hx 1

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `supSpanSingleton_apply_of_mem` / 定理 `supSpanSingleton_apply_of_mem`

English:
theorem supSpanSingleton_apply_of_mem
  statement: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  proof: by
  simpa using supSpanSingleton_apply_mk f x y hx x' hx' 0

中文:
定理 supSpanSingleton_apply_of_mem
  结论: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  证明: by
  simpa using supSpanSingleton_apply_mk f x y hx x' hx' 0

Depends on / 依赖: supSpanSingleton_apply_mk
-/
theorem supSpanSingleton_apply_of_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (x' : (f.supSpanSingleton x y hx).domain) (hx' : (x' : E) in f.domain) :
    f.supSpanSingleton x y hx x' = f ⟨x', hx'⟩ := by
  simpa using supSpanSingleton_apply_mk f x y hx x' hx' 0

/--
theorem `supSpanSingleton_apply_mk_of_mem` / 定理 `supSpanSingleton_apply_mk_of_mem`

English:
theorem supSpanSingleton_apply_mk_of_mem
  statement: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  proof: supSpanSingleton_apply_of_mem f y hx _ hx'

中文:
定理 supSpanSingleton_apply_mk_of_mem
  结论: (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
  证明: supSpanSingleton_apply_of_mem f y hx _ hx'

Depends on / 依赖: supSpanSingleton_apply_of_mem
-/
theorem supSpanSingleton_apply_mk_of_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain)
    {x' : E} (hx' : (x' : E) in f.domain) :
    f.supSpanSingleton x y hx ⟨x', mem_sup_left hx'⟩ = f ⟨x', hx'⟩ :=
  supSpanSingleton_apply_of_mem f y hx _ hx'

end

set_option backward.privateInPublic true in
/--
theorem `sSup_aux` / 定理 `sSup_aux`

English:
theorem sSup_aux
  given: (c : Set (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c)
  proof: by
  rcases c.eq_empty_or_nonempty with rfl | cne
  · simp
  have hdir : DirectedOn (· <= ·) (domain '' c) :=
    directedOn_image.2 (hc.mono @(domain_mono.monotone))
  have P : forall x : ↥(sSup (domain '' c)), { p : c // (x : E) in p.val.domain } := by
    rintro x
    apply Classical.indefiniteDe

中文:
定理 sSup_aux
  条件: (c : 集合 (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c)
  证明: by
  rcases c.eq_empty_or_nonempty with rfl | cne
  · simp
  have hdir : DirectedOn (· <= ·) (domain '' c) :=
    directedOn_image.2 (hc.mono @(domain_mono.monotone))
  have P : forall x : ↥(sSup (domain '' c)), { p : c // (x : E) in p.val.domain } := by
    rintro x
    apply Classical.indefiniteDe
-/
private theorem sSup_aux (c : Set (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c) :
    exists f : ↥(sSup (domain '' c)) ->ₛₗ[σ] F, (⟨_, f⟩ : E ->ₛₗ.[σ] F) in upperBounds c := by
  rcases c.eq_empty_or_nonempty with rfl | cne
  · simp
  have hdir : DirectedOn (· <= ·) (domain '' c) :=
    directedOn_image.2 (hc.mono @(domain_mono.monotone))
  have P : forall x : ↥(sSup (domain '' c)), { p : c // (x : E) in p.val.domain } := by
    rintro x
    apply Classical.indefiniteDescription
    have := (mem_sSup_of_directed (cne.image _) hdir).1 x.2
    rwa [Set.exists_mem_image, ← bex_def, SetCoe.exists'] at this
  set f : ↥(sSup (domain '' c)) -> F := fun x => (P x).val.val ⟨x, (P x).property⟩
  have f_eq : forall (p : c) (x : ↥(sSup (domain '' c))) (y : p.1.1) (_hxy : (x : E) = y),
      f x = p.1 y := by
    intro p x y hxy
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, _hqc, ⟨hxq1, hxq2⟩, ⟨hpq1, hpq2⟩⟩
    exact (hxq2 (y := ⟨y, hpq1 y.2⟩) hxy).trans (hpq2 rfl).symm
  use { toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_
  · intro x y
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩
    set x' := inclusion hpx.1 ⟨x, (P x).2⟩
    set y' := inclusion hpy.1 ⟨y, (P y).2⟩
    rw [f_eq ⟨p]; rw [hpc⟩ x x' rfl]; rw [f_eq ⟨p]; rw [hpc⟩ y y' rfl]; rw [f_eq ⟨p]; rw [hpc⟩ (x + y) (x' + y') rfl]; rw [map_add]
  · intro c x
    rw [f_eq (P x).1 (c • x) (c • ⟨x]; rw [(P x).2⟩) rfl]; rw [← map_smulₛₗ]
  · intro p hpc
refine ⟨le_sSup Set.mem_image_of_mem domain hpc, fun x y hxy => Eq.symm ?_⟩
    exact f_eq ⟨p, hpc⟩ _ _ hxy.symm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def sSup (c : Set (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c)
  body: ⟨_, Classical.choose sSup_aux c hc⟩

中文:
定义 noncomputable
  签名: def sSup (c : 集合 (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c)
  定义体: ⟨_, Classical.choose sSup_aux c hc⟩
-/
protected noncomputable def sSup (c : Set (E ->ₛₗ.[σ] F)) (hc : DirectedOn (· <= ·) c) :
    E ->ₛₗ.[σ] F :=
⟨_, Classical.choose sSup_aux c hc⟩

/--
theorem `domain_sSup` / 定理 `domain_sSup`

English:
theorem domain_sSup
  given: {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c)
  proof: rfl

中文:
定理 domain_sSup
  条件: {c : 集合 (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c)
  证明: rfl
-/
theorem domain_sSup {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) :
    (LinearPMap.sSup c hc).domain = sSup (LinearPMap.domain '' c) := rfl

/--
theorem `mem_domain_sSup_iff` / 定理 `mem_domain_sSup_iff`

English:
theorem mem_domain_sSup_iff
  statement: {c : Set (E ->ₛₗ.[σ] F)} (hnonempty : c.Nonempty)
  proof: by
  rw [domain_sSup]; rw [Submodule.mem_sSup_of_directed (hnonempty.image _)
    (DirectedOn.mono_comp LinearPMap.domain_mono.monotone hc)]
  simp

中文:
定理 mem_domain_sSup_iff
  结论: {c : 集合 (E ->ₛₗ.[σ] F)} (hnonempty : c.非空)
  证明: by
  rw [domain_sSup]; rw [Submodule.mem_sSup_of_directed (hnonempty.image _)
    (DirectedOn.mono_comp LinearPMap.domain_mono.monotone hc)]
  simp

Depends on / 依赖: DirectedOn, DirectedOn.mono_comp, LinearPMap, LinearPMap.domain_mono.monotone, Submodule, Submodule.mem_sSup_of_directed, domain_mono, domain_sSup, hnonempty, hnonempty.image, mem_sSup_of_directed, mono_comp, monotone
-/
theorem mem_domain_sSup_iff {c : Set (E ->ₛₗ.[σ] F)} (hnonempty : c.Nonempty)
    (hc : DirectedOn (· <= ·) c) {x : E} :
    x in (LinearPMap.sSup c hc).domain ↔ exists f in c, x in f.domain := by
  rw [domain_sSup]; rw [Submodule.mem_sSup_of_directed (hnonempty.image _)
    (DirectedOn.mono_comp LinearPMap.domain_mono.monotone hc)]
  simp

/--
theorem `le_sSup` / 定理 `le_sSup`

English:
theorem le_sSup
  statement: {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {f : E ->ₛₗ.[σ] F}
  proof: Classical.choose_spec (sSup_aux c hc) hf

中文:
定理 le_sSup
  结论: {c : 集合 (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {f : E ->ₛₗ.[σ] F}
  证明: Classical.choose_spec (sSup_aux c hc) hf
-/
protected theorem le_sSup {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {f : E ->ₛₗ.[σ] F}
    (hf : f in c) : f <= LinearPMap.sSup c hc :=
  Classical.choose_spec (sSup_aux c hc) hf

/--
theorem `sSup_le` / 定理 `sSup_le`

English:
theorem sSup_le
  statement: {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {g : E ->ₛₗ.[σ] F}
  proof: le_of_eqLocus_ge
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f <= LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1

中文:
定理 sSup_le
  结论: {c : 集合 (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {g : E ->ₛₗ.[σ] F}
  证明: le_of_eqLocus_ge
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f <= LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1
-/
protected theorem sSup_le {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {g : E ->ₛₗ.[σ] F}
    (hg : forall f in c, f <= g) : LinearPMap.sSup c hc <= g :=
le_of_eqLocus_ge
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f <= LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1

/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  statement: {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {l : E ->ₛₗ.[σ] F}
  proof: by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl

中文:
定理 sSup_apply
  结论: {c : 集合 (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {l : E ->ₛₗ.[σ] F}
  证明: by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl
-/
protected theorem sSup_apply {c : Set (E ->ₛₗ.[σ] F)} (hc : DirectedOn (· <= ·) c) {l : E ->ₛₗ.[σ] F}
    (hl : l in c) (x : l.domain) :
    (LinearPMap.sSup c hc) ⟨x, (LinearPMap.le_sSup hc hl).1 x.2⟩ = l x := by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl

end LinearPMap

namespace LinearMap

/--
Definition of `toPMap` / `toPMap` 的定义

English:
definition toPMap
  signature: (f : E ->ₛₗ[σ] F) (p : Submodule R E)
  body: ⟨p, f.comp p.subtype⟩

@[simp]

中文:
定义 toPMap
  签名: (f : E ->ₛₗ[σ] F) (p : 子模 R E)
  定义体: ⟨p, f.comp p.subtype⟩

@[simp]

Depends on / 依赖: f.comp, p.subtype, subtype
-/
def toPMap (f : E ->ₛₗ[σ] F) (p : Submodule R E) : E ->ₛₗ.[σ] F :=
  ⟨p, f.comp p.subtype⟩

@[simp]
/--
theorem `toPMap_apply` / 定理 `toPMap_apply`

English:
theorem toPMap_apply
  given: (f : E ->ₛₗ[σ] F) (p : Submodule R E) (x : p)
  statement: f.toPMap p x = f x
  proof: rfl

@[simp]

中文:
定理 toPMap_apply
  条件: (f : E ->ₛₗ[σ] F) (p : 子模 R E) (x : p)
  结论: f.toPMap p x = f x
  证明: rfl

@[simp]
-/
theorem toPMap_apply (f : E ->ₛₗ[σ] F) (p : Submodule R E) (x : p) : f.toPMap p x = f x :=
  rfl

@[simp]
/--
theorem `toPMap_domain` / 定理 `toPMap_domain`

English:
theorem toPMap_domain
  given: (f : E ->ₛₗ[σ] F) (p : Submodule R E)
  statement: (f.toPMap p).domain = p
  proof: rfl

中文:
定理 toPMap_domain
  条件: (f : E ->ₛₗ[σ] F) (p : 子模 R E)
  结论: (f.toPMap p).domain = p
  证明: rfl
-/
theorem toPMap_domain (f : E ->ₛₗ[σ] F) (p : Submodule R E) : (f.toPMap p).domain = p :=
  rfl

/--
Definition of `compPMap` / `compPMap` 的定义

English:
definition compPMap
  signature: {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F)
  body: f.domain
  toFun := g.comp f.toFun

@[simp]

中文:
定义 compPMap
  签名: {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F)
  定义体: f.domain
  toFun := g.comp f.toFun

@[simp]

Depends on / 依赖: domain, f.domain
-/
def compPMap {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F) :
    E ->ₛₗ.[ρ] G where
  domain := f.domain
  toFun := g.comp f.toFun

@[simp]
/--
theorem `compPMap_apply` / 定理 `compPMap_apply`

English:
theorem compPMap_apply
  given: (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F) (x)
  proof: { comp_eq := rfl }
    g.compPMap (ρ := τ.comp σ) f x = g (f x) :=
  rfl

中文:
定理 compPMap_apply
  条件: (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F) (x)
  证明: { comp_eq := rfl }
    g.compPMap (ρ := τ.comp σ) f x = g (f x) :=
  rfl

Depends on / 依赖: comp_eq
-/
theorem compPMap_apply (g : F ->ₛₗ[τ] G) (f : E ->ₛₗ.[σ] F) (x) :
    letI : RingHomCompTriple σ τ (τ.comp σ) := { comp_eq := rfl }
    g.compPMap (ρ := τ.comp σ) f x = g (f x) :=
  rfl

end LinearMap

namespace LinearPMap

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : E ->ₛₗ.[σ] F) (p : Submodule S F) (H : forall x, f x in p)
  body: f.domain
  toFun := f.toFun.codRestrict p H

中文:
定义 codRestrict
  签名: (f : E ->ₛₗ.[σ] F) (p : 子模 S F) (H : 对任意 x, f x in p)
  定义体: f.domain
  toFun := f.toFun.codRestrict p H

Depends on / 依赖: domain, f.domain
-/
def codRestrict (f : E ->ₛₗ.[σ] F) (p : Submodule S F) (H : forall x, f x in p) : E ->ₛₗ.[σ] p where
  domain := f.domain
  toFun := f.toFun.codRestrict p H

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ.[τ] G) (f : E ->ₛₗ.[σ] F)
  body: g.toFun.compPMap f.codRestrict _ H

中文:
定义 comp
  签名: {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ.[τ] G) (f : E ->ₛₗ.[σ] F)
  定义体: g.toFun.compPMap f.codRestrict _ H

Depends on / 依赖: codRestrict, compPMap, f.codRestrict, g.toFun.compPMap
-/
def comp {ρ : R ->+* T} [RingHomCompTriple σ τ ρ] (g : F ->ₛₗ.[τ] G) (f : E ->ₛₗ.[σ] F)
    (H : forall x : f.domain, f x in g.domain) : E ->ₛₗ.[ρ] G :=
g.toFun.compPMap f.codRestrict _ H

/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G)
  body: f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

omit [Module S F] in
@[

中文:
定义 coprod
  签名: [模 R F] [模 S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G)
  定义体: f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

omit [Module S F] in
@[

Depends on / 依赖: domain, f.domain.prod, g.domain
-/
def coprod [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G) : E × F ->ₛₗ.[σ] G where
  domain := f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain ->ₛₗ[σ] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

omit [Module S F] in
@[simp]
/--
theorem `coprod_apply` / 定理 `coprod_apply`

English:
theorem coprod_apply
  given: [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G) (x)
  proof: rfl

中文:
定理 coprod_apply
  条件: [模 R F] [模 S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G) (x)
  证明: rfl
-/
theorem coprod_apply [Module R F] [Module S G] (f : E ->ₛₗ.[σ] G) (g : F ->ₛₗ.[σ] G) (x) :
    f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : E ->ₛₗ.[σ] F) (S : Submodule R E)
  body: ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩

@[simp]

中文:
定义 domRestrict
  签名: (f : E ->ₛₗ.[σ] F) (S : 子模 R E)
  定义体: ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, domain, f.domain, f.toFun.comp, inclusion
-/
def domRestrict (f : E ->ₛₗ.[σ] F) (S : Submodule R E) : E ->ₛₗ.[σ] F :=
  ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩

@[simp]
/--
theorem `domRestrict_domain` / 定理 `domRestrict_domain`

English:
theorem domRestrict_domain
  given: (f : E ->ₛₗ.[σ] F) {S : Submodule R E}
  proof: rfl

中文:
定理 domRestrict_domain
  条件: (f : E ->ₛₗ.[σ] F) {S : 子模 R E}
  证明: rfl
-/
theorem domRestrict_domain (f : E ->ₛₗ.[σ] F) {S : Submodule R E} :
    (f.domRestrict S).domain = S ⊓ f.domain :=
  rfl

/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: {f : E ->ₛₗ.[σ] F} {S : Submodule R E} ⦃x
  statement: ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
  proof: by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _

中文:
定理 domRestrict_apply
  条件: {f : E ->ₛₗ.[σ] F} {S : 子模 R E} ⦃x
  结论: ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
  证明: by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _

Depends on / 依赖: LinearPMap, LinearPMap.mk_apply, Submodule, Submodule.inclusion, inclusion, mk_apply
-/
theorem domRestrict_apply {f : E ->ₛₗ.[σ] F} {S : Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
    (h : (x : E) = y) : f.domRestrict S x = f y := by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _

/--
theorem `domRestrict_le` / 定理 `domRestrict_le`

English:
theorem domRestrict_le
  given: {f : E ->ₛₗ.[σ] F} {S : Submodule R E}
  statement: f.domRestrict S <= f
  proof: ⟨by simp, fun _ _ hxy => domRestrict_apply hxy⟩

中文:
定理 domRestrict_le
  条件: {f : E ->ₛₗ.[σ] F} {S : 子模 R E}
  结论: f.domRestrict S <= f
  证明: ⟨by simp, fun _ _ hxy => domRestrict_apply hxy⟩

Depends on / 依赖: domRestrict_apply
-/
theorem domRestrict_le {f : E ->ₛₗ.[σ] F} {S : Submodule R E} : f.domRestrict S <= f :=
  ⟨by simp, fun _ _ hxy => domRestrict_apply hxy⟩

/-! ### Graph -/


section Graph

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: [Module R F] (f : E ->ₗ.[R] F)
  body: f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F ->ₗ[R] F))

中文:
定义 graph
  签名: [模 R F] (f : E ->ₗ.[R] F)
  定义体: f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F ->ₗ[R] F))

Depends on / 依赖: LinearMap, LinearMap.id, domain, f.domain.subtype.prodMap, f.toFun.graph.map, prodMap, subtype
-/
def graph [Module R F] (f : E ->ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F ->ₗ[R] F))

/--
theorem `mem_graph_iff'` / 定理 `mem_graph_iff'`

English:
theorem mem_graph_iff'
  given: [Module R F] (f : E ->ₗ.[R] F) {x : E × F}
  proof: by simp [graph]

@[simp, grind =]

中文:
定理 mem_graph_iff'
  条件: [模 R F] (f : E ->ₗ.[R] F) {x : E × F}
  证明: by simp [graph]

@[simp, grind =]
-/
theorem mem_graph_iff' [Module R F] (f : E ->ₗ.[R] F) {x : E × F} :
    x in f.graph ↔ exists y : f.domain, (↑y, f y) = x := by simp [graph]

@[simp, grind =]
/--
theorem `mem_graph_iff` / 定理 `mem_graph_iff`

English:
theorem mem_graph_iff
  given: [Module R F] (f : E ->ₗ.[R] F) {x : E × F}
  proof: by
  cases x
  simp_rw [mem_graph_iff', Prod.mk_inj]

中文:
定理 mem_graph_iff
  条件: [模 R F] (f : E ->ₗ.[R] F) {x : E × F}
  证明: by
  cases x
  simp_rw [mem_graph_iff', Prod.mk_inj]

Depends on / 依赖: Prod.mk_inj, mem_graph_iff, mk_inj, simp_rw
-/
theorem mem_graph_iff [Module R F] (f : E ->ₗ.[R] F) {x : E × F} :
    x in f.graph ↔ exists y : f.domain, (↑y : E) = x.1 ∧ f y = x.2 := by
  cases x
  simp_rw [mem_graph_iff', Prod.mk_inj]

/--
theorem `mem_graph` / 定理 `mem_graph`

English:
theorem mem_graph
  given: [Module R F] (f : E ->ₗ.[R] F) (x : domain f)
  statement: ((x : E), f x) in f.graph
  proof: by simp

中文:
定理 mem_graph
  条件: [模 R F] (f : E ->ₗ.[R] F) (x : domain f)
  结论: ((x : E), f x) in f.graph
  证明: by simp
-/
theorem mem_graph [Module R F] (f : E ->ₗ.[R] F) (x : domain f) : ((x : E), f x) in f.graph := by simp

/--
theorem `graph_map_fst_eq_domain` / 定理 `graph_map_fst_eq_domain`

English:
theorem graph_map_fst_eq_domain
  given: [Module R F] (f : E ->ₗ.[R] F)
  proof: by
  ext x
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor <;> intro h
  · rcases h with ⟨x, hx, _⟩
    exact hx
  · use f ⟨x, h⟩
    simp only [h, exists_const]

中文:
定理 graph_map_fst_eq_domain
  条件: [模 R F] (f : E ->ₗ.[R] F)
  证明: by
  ext x
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor <;> intro h
  · rcases h with ⟨x, hx, _⟩
    exact hx
  · use f ⟨x, h⟩
    simp only [h, exists_const]

Depends on / 依赖: LinearMap, LinearMap.fst_apply, Prod.exists, Submodule, Submodule.mem_map, Subtype, Subtype.exists, exists_and_left, exists_and_right, exists_const, exists_eq_left, exists_eq_right, fst_apply, mem_graph_iff, mem_map
-/
theorem graph_map_fst_eq_domain [Module R F] (f : E ->ₗ.[R] F) :
    f.graph.map (LinearMap.fst R E F) = f.domain := by
  ext x
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor <;> intro h
  · rcases h with ⟨x, hx, _⟩
    exact hx
  · use f ⟨x, h⟩
    simp only [h, exists_const]

/--
theorem `graph_map_snd_eq_range` / 定理 `graph_map_snd_eq_range`

English:
theorem graph_map_snd_eq_range
  given: [Module R F] (f : E ->ₗ.[R] F)
  proof: by ext; simp

中文:
定理 graph_map_snd_eq_range
  条件: [模 R F] (f : E ->ₗ.[R] F)
  证明: by ext; simp
-/
theorem graph_map_snd_eq_range [Module R F] (f : E ->ₗ.[R] F) :
    f.graph.map (LinearMap.snd R E F) = LinearMap.range f.toFun := by ext; simp

variable {M : Type*} [Monoid M] [DistribMulAction M F] [Module R F] [SMulCommClass R M F] (y : M)

/--
theorem `smul_graph` / 定理 `smul_graph`

English:
theorem smul_graph
  given: (f : E ->ₗ.[R] F) (z : M)
  proof: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.smul_apply, Prod.mk_inj, Prod.exists,

中文:
定理 smul_graph
  条件: (f : E ->ₗ.[R] F) (z : M)
  证明: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.smul_apply, Prod.mk_inj, Prod.exists,

Depends on / 依赖: LinearMap, LinearMap.id_coe, LinearMap.prodMap_apply, LinearMap.smul_apply, LinearPMap, LinearPMap.smul_apply, Prod.exists, Prod.mk_inj, Submodule, Submodule.mem_map, exists_exists_and_eq_and, id_coe, mem_graph_iff, mem_map, mk_inj, prodMap_apply, smul_apply, x_fst, x_snd
-/
theorem smul_graph (f : E ->ₗ.[R] F) (z : M) :
    (z • f).graph =
      f.graph.map ((LinearMap.id : E ->ₗ[R] E).prodMap (z • (LinearMap.id : F ->ₗ[R] F))) := by
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
  rw [← h.1]; rw [← h.2]
  simp [hy, hx']

/--
theorem `neg_graph` / 定理 `neg_graph`

English:
theorem neg_graph
  given: (f : E ->ₗ.[R] F)
  proof: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.neg_apply, Prod.mk_inj, Prod.exists, e

中文:
定理 neg_graph
  条件: (f : E ->ₗ.[R] F)
  证明: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.neg_apply, Prod.mk_inj, Prod.exists, e

Depends on / 依赖: LinearMap, LinearMap.id_coe, LinearMap.neg_apply, LinearMap.prodMap_apply, LinearPMap, LinearPMap.neg_apply, Prod.exists, Prod.mk_inj, Submodule, Submodule.mem_map, exists_exists_and_eq_and, id_coe, mem_graph_iff, mem_map, mk_inj, neg_apply, prodMap_apply, x_fst, x_snd
-/
theorem neg_graph (f : E ->ₗ.[R] F) :
    (-f).graph =
    f.graph.map ((LinearMap.id : E ->ₗ[R] E).prodMap (-(LinearMap.id : F ->ₗ[R] F))) := by
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
  rw [← h.1]; rw [← h.2]
  simp [hy, hx']

/--
theorem `mem_graph_snd_inj` / 定理 `mem_graph_snd_inj`

English:
theorem mem_graph_snd_inj
  statement: (f : E ->ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') in f.graph)
  proof: by
  grind

中文:
定理 mem_graph_snd_inj
  结论: (f : E ->ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') in f.graph)
  证明: by
  grind
-/
theorem mem_graph_snd_inj (f : E ->ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') in f.graph)
    (hy : (y, y') in f.graph) (hxy : x = y) : x' = y' := by
  grind

/--
theorem `mem_graph_snd_inj'` / 定理 `mem_graph_snd_inj'`

English:
theorem mem_graph_snd_inj'
  statement: (f : E ->ₗ.[R] F) {x y : E × F} (hx : x in f.graph) (hy : y in f.graph)
  proof: by
  grind

中文:
定理 mem_graph_snd_inj'
  结论: (f : E ->ₗ.[R] F) {x y : E × F} (hx : x in f.graph) (hy : y in f.graph)
  证明: by
  grind
-/
theorem mem_graph_snd_inj' (f : E ->ₗ.[R] F) {x y : E × F} (hx : x in f.graph) (hy : y in f.graph)
    (hxy : x.1 = y.1) : x.2 = y.2 := by
  grind

/--
theorem `graph_fst_eq_zero_snd` / 定理 `graph_fst_eq_zero_snd`

English:
theorem graph_fst_eq_zero_snd
  statement: (f : E ->ₗ.[R] F) {x : E} {x' : F} (h : (x, x') in f.graph)
  proof: f.mem_graph_snd_inj h f.graph.zero_mem hx

中文:
定理 graph_fst_eq_zero_snd
  结论: (f : E ->ₗ.[R] F) {x : E} {x' : F} (h : (x, x') in f.graph)
  证明: f.mem_graph_snd_inj h f.graph.zero_mem hx

Depends on / 依赖: f.graph.zero_mem, f.mem_graph_snd_inj, mem_graph_snd_inj, zero_mem
-/
theorem graph_fst_eq_zero_snd (f : E ->ₗ.[R] F) {x : E} {x' : F} (h : (x, x') in f.graph)
    (hx : x = 0) : x' = 0 :=
  f.mem_graph_snd_inj h f.graph.zero_mem hx

/--
theorem `mem_domain_iff` / 定理 `mem_domain_iff`

English:
theorem mem_domain_iff
  given: {f : E ->ₗ.[R] F} {x : E}
  statement: x in f.domain ↔ exists y : F, (x, y) in f.graph
  proof: by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  grind

中文:
定理 mem_domain_iff
  条件: {f : E ->ₗ.[R] F} {x : E}
  结论: x in f.domain ↔ 存在 y : F, (x, y) in f.graph
  证明: by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  grind

Depends on / 依赖: f.mem_graph, mem_graph
-/
theorem mem_domain_iff {f : E ->ₗ.[R] F} {x : E} : x in f.domain ↔ exists y : F, (x, y) in f.graph := by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  grind

/--
theorem `mem_domain_of_mem_graph` / 定理 `mem_domain_of_mem_graph`

English:
theorem mem_domain_of_mem_graph
  given: {f : E ->ₗ.[R] F} {x : E} {y : F} (h : (x, y) in f.graph)
  proof: by
  rw [mem_domain_iff]
  exact ⟨y, h⟩

中文:
定理 mem_domain_of_mem_graph
  条件: {f : E ->ₗ.[R] F} {x : E} {y : F} (h : (x, y) in f.graph)
  证明: by
  rw [mem_domain_iff]
  exact ⟨y, h⟩

Depends on / 依赖: mem_domain_iff
-/
theorem mem_domain_of_mem_graph {f : E ->ₗ.[R] F} {x : E} {y : F} (h : (x, y) in f.graph) :
    x in f.domain := by
  rw [mem_domain_iff]
  exact ⟨y, h⟩

/--
theorem `image_iff` / 定理 `image_iff`

English:
theorem image_iff
  given: {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : x in f.domain)
  proof: by
  grind

中文:
定理 image_iff
  条件: {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : x in f.domain)
  证明: by
  grind
-/
theorem image_iff {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : x in f.domain) :
    y = f ⟨x, hx⟩ ↔ (x, y) in f.graph := by
  grind

/--
theorem `mem_range_iff` / 定理 `mem_range_iff`

English:
theorem mem_range_iff
  given: {f : E ->ₗ.[R] F} {y : F}
  statement: y in Set.range f ↔ exists x : E, (x, y) in f.graph
  proof: by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  grind

中文:
定理 mem_range_iff
  条件: {f : E ->ₗ.[R] F} {y : F}
  结论: y in 集合.range f ↔ 存在 x : E, (x, y) in f.graph
  证明: by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  grind

Depends on / 依赖: Set.mem_range, f.mem_graph, mem_graph, mem_range
-/
theorem mem_range_iff {f : E ->ₗ.[R] F} {y : F} : y in Set.range f ↔ exists x : E, (x, y) in f.graph := by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  grind

/--
theorem `mem_domain_iff_of_eq_graph` / 定理 `mem_domain_iff_of_eq_graph`

English:
theorem mem_domain_iff_of_eq_graph
  given: {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) {x : E}
  proof: by simp_rw [mem_domain_iff, h]

中文:
定理 mem_domain_iff_of_eq_graph
  条件: {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) {x : E}
  证明: by simp_rw [mem_domain_iff, h]

Depends on / 依赖: mem_domain_iff, simp_rw
-/
theorem mem_domain_iff_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) {x : E} :
    x in f.domain ↔ x in g.domain := by simp_rw [mem_domain_iff, h]

/--
theorem `le_of_le_graph` / 定理 `le_of_le_graph`

English:
theorem le_of_le_graph
  given: {f g : E ->ₗ.[R] F} (h : f.graph <= g.graph)
  statement: f <= g
  proof: by
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

中文:
定理 le_of_le_graph
  条件: {f g : E ->ₗ.[R] F} (h : f.graph <= g.graph)
  结论: f <= g
  证明: by
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

Depends on / 依赖: image_iff, mem_domain_iff
-/
theorem le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.graph <= g.graph) : f <= g := by
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

/--
theorem `le_graph_of_le` / 定理 `le_graph_of_le`

English:
theorem le_graph_of_le
  given: {f g : E ->ₗ.[R] F} (h : f <= g)
  statement: f.graph <= g.graph
  proof: by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert! hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]

中文:
定理 le_graph_of_le
  条件: {f g : E ->ₗ.[R] F} (h : f <= g)
  结论: f.graph <= g.graph
  证明: by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert! hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]

Depends on / 依赖: convert, mem_graph_iff, true_and
-/
theorem le_graph_of_le {f g : E ->ₗ.[R] F} (h : f <= g) : f.graph <= g.graph := by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert! hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]

/--
theorem `le_graph_iff` / 定理 `le_graph_iff`

English:
theorem le_graph_iff
  given: {f g : E ->ₗ.[R] F}
  statement: f.graph <= g.graph ↔ f <= g
  proof: ⟨le_of_le_graph, le_graph_of_le⟩

中文:
定理 le_graph_iff
  条件: {f g : E ->ₗ.[R] F}
  结论: f.graph <= g.graph ↔ f <= g
  证明: ⟨le_of_le_graph, le_graph_of_le⟩

Depends on / 依赖: le_graph_of_le, le_of_le_graph
-/
theorem le_graph_iff {f g : E ->ₗ.[R] F} : f.graph <= g.graph ↔ f <= g :=
  ⟨le_of_le_graph, le_graph_of_le⟩

/--
theorem `eq_of_eq_graph` / 定理 `eq_of_eq_graph`

English:
theorem eq_of_eq_graph
  given: {f g : E ->ₗ.[R] F} (h : f.graph = g.graph)
  statement: f = g
  proof: by
  apply dExt
  · ext
    exact mem_domain_iff_of_eq_graph h
  · apply (le_of_le_graph h.le).2

中文:
定理 eq_of_eq_graph
  条件: {f g : E ->ₗ.[R] F} (h : f.graph = g.graph)
  结论: f = g
  证明: by
  apply dExt
  · ext
    exact mem_domain_iff_of_eq_graph h
  · apply (le_of_le_graph h.le).2

Depends on / 依赖: h.le, le_of_le_graph, mem_domain_iff_of_eq_graph
-/
theorem eq_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.graph = g.graph) : f = g := by
  apply dExt
  · ext
    exact mem_domain_iff_of_eq_graph h
  · apply (le_of_le_graph h.le).2

end Graph

end LinearPMap

namespace Submodule

section SubmoduleToLinearPMap

variable [Module R F]

/--
theorem `existsUnique_from_graph` / 定理 `existsUnique_from_graph`

English:
theorem existsUnique_from_graph
  statement: {g : Submodule R (E × F)}
  proof: by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · convert! ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) in g := by
    convert! g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))

中文:
定理 存在Unique_from_graph
  结论: {g : 子模 R (E × F)}
  证明: by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · convert! ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) in g := by
    convert! g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))

Depends on / 依赖: convert, existsUnique_of_exists_of_unique, g.sub_mem, sub_eq_zero, sub_eq_zero.mp, sub_mem, sub_self
-/
theorem existsUnique_from_graph {g : Submodule R (E × F)}
    (hg : forall {x : E × F} (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a in g.map (LinearMap.fst R E F)) : exists! b : F, (a, b) in g := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · convert! ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) in g := by
    convert! g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))

/--
Definition of `valFromGraph` / `valFromGraph` 的定义

English:
definition valFromGraph
  signature: {g : Submodule R (E × F)}
  body: (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose

中文:
定义 valFromGraph
  签名: {g : 子模 R (E × F)}
  定义体: (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose

Depends on / 依赖: ExistsUnique, ExistsUnique.exists, existsUnique_from_graph
-/
noncomputable def valFromGraph {g : Submodule R (E × F)}
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a in g.map (LinearMap.fst R E F)) : F :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose

/--
theorem `valFromGraph_mem` / 定理 `valFromGraph_mem`

English:
theorem valFromGraph_mem
  statement: {g : Submodule R (E × F)}
  proof: (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec

中文:
定理 valFromGraph_mem
  结论: {g : 子模 R (E × F)}
  证明: (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec

Depends on / 依赖: ExistsUnique, ExistsUnique.exists, choose_spec, existsUnique_from_graph
-/
theorem valFromGraph_mem {g : Submodule R (E × F)}
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a in g.map (LinearMap.fst R E F)) : (a, valFromGraph hg ha) in g :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec

/--
Definition of `toLinearPMapAux` / `toLinearPMapAux` 的定义

English:
definition toLinearPMapAux
  signature: (g : Submodule R (E × F))
  body: fun x => valFromGraph hg x.2
  map_add' := fun v w => by
    have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
    have hvw := valFromGraph_mem hg hadd
    have hvw' := g.add_mem (valFromGraph_mem hg v.2) (valFromGraph_mem hg w.2)
    rw [Prod.mk_add_mk] at hvw'
    exact (existsUnique_from

中文:
定义 toLinearPMapAux
  签名: (g : 子模 R (E × F))
  定义体: fun x => valFromGraph hg x.2
  map_add' := fun v w => by
    have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
    have hvw := valFromGraph_mem hg hadd
    have hvw' := g.add_mem (valFromGraph_mem hg v.2) (valFromGraph_mem hg w.2)
    rw [Prod.mk_add_mk] at hvw'
    exact (existsUnique_from

Depends on / 依赖: valFromGraph
-/
noncomputable def toLinearPMapAux (g : Submodule R (E × F))
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) :
    g.map (LinearMap.fst R E F) ->ₗ[R] F where
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
/--
Definition of `toLinearPMap` / `toLinearPMap` 的定义

English:
definition toLinearPMap
  signature: (g : Submodule R (E × F))
  body: g.map (LinearMap.fst R E F)
  toFun := if hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0

中文:
定义 toLinearPMap
  签名: (g : 子模 R (E × F))
  定义体: g.map (LinearMap.fst R E F)
  toFun := if hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0

Depends on / 依赖: LinearMap, LinearMap.fst, g.map
-/
noncomputable def toLinearPMap (g : Submodule R (E × F)) : E ->ₗ.[R] F where
  domain := g.map (LinearMap.fst R E F)
  toFun := if hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0

/--
theorem `toLinearPMap_domain` / 定理 `toLinearPMap_domain`

English:
theorem toLinearPMap_domain
  given: (g : Submodule R (E × F))
  proof: rfl

中文:
定理 toLinearPMap_domain
  条件: (g : 子模 R (E × F))
  证明: rfl
-/
theorem toLinearPMap_domain (g : Submodule R (E × F)) :
    g.toLinearPMap.domain = g.map (LinearMap.fst R E F) := rfl

/--
theorem `toLinearPMap_apply_aux` / 定理 `toLinearPMap_apply_aux`

English:
theorem toLinearPMap_apply_aux
  statement: {g : Submodule R (E × F)}
  proof: by
  classical
  change (if hg : _ then g.toLinearPMapAux hg else 0) x = _
  rw [dif_pos]
  · rfl
  · exact hg

中文:
定理 toLinearPMap_apply_aux
  结论: {g : 子模 R (E × F)}
  证明: by
  classical
  change (if hg : _ then g.toLinearPMapAux hg else 0) x = _
  rw [dif_pos]
  · rfl
  · exact hg

Depends on / 依赖: classical, dif_pos, g.toLinearPMapAux, toLinearPMapAux
-/
theorem toLinearPMap_apply_aux {g : Submodule R (E × F)}
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) :
    g.toLinearPMap x = valFromGraph hg x.2 := by
  classical
  change (if hg : _ then g.toLinearPMapAux hg else 0) x = _
  rw [dif_pos]
  · rfl
  · exact hg

/--
theorem `mem_graph_toLinearPMap` / 定理 `mem_graph_toLinearPMap`

English:
theorem mem_graph_toLinearPMap
  statement: {g : Submodule R (E × F)}
  proof: by
  rw [toLinearPMap_apply_aux hg]
  exact valFromGraph_mem hg x.2

中文:
定理 mem_graph_toLinearPMap
  结论: {g : 子模 R (E × F)}
  证明: by
  rw [toLinearPMap_apply_aux hg]
  exact valFromGraph_mem hg x.2

Depends on / 依赖: toLinearPMap_apply_aux, valFromGraph_mem
-/
theorem mem_graph_toLinearPMap {g : Submodule R (E × F)}
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) : (x.val, g.toLinearPMap x) in g := by
  rw [toLinearPMap_apply_aux hg]
  exact valFromGraph_mem hg x.2

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toLinearPMap_graph_eq` / 定理 `toLinearPMap_graph_eq`

English:
theorem toLinearPMap_graph_eq
  statement: (g : Submodule R (E × F))
  proof: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert! g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  have hx_fst : x_fst in g.map (LinearMap.fst R E F) := 

中文:
定理 toLinearPMap_graph_eq
  结论: (g : 子模 R (E × F))
  证明: by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert! g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  have hx_fst : x_fst in g.map (LinearMap.fst R E F) := 

Depends on / 依赖: LinearMap, LinearMap.fst, LinearMap.fst_apply, LinearPMap, LinearPMap.mem_graph_iff, Prod.exists, Prod.ext, Subtype, Subtype.coe_mk, coe_mk, convert, existsUnique_fro, exists_and_right, exists_eq_right, fst_apply, g.map, g.mem_graph_toLinearPMap, hx1.symm, hx2.symm, hx_fst
-/
theorem toLinearPMap_graph_eq (g : Submodule R (E × F))
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) :
    g.toLinearPMap.graph = g := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert! g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  have hx_fst : x_fst in g.map (LinearMap.fst R E F) := by
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨x_snd, hx⟩
  refine ⟨⟨x_fst, hx_fst⟩, Subtype.coe_mk x_fst hx_fst, ?_⟩
  rw [toLinearPMap_apply_aux hg]
  exact (existsUnique_from_graph @hg hx_fst).unique (valFromGraph_mem hg hx_fst) hx

/--
theorem `toLinearPMap_range` / 定理 `toLinearPMap_range`

English:
theorem toLinearPMap_range
  statement: (g : Submodule R (E × F))
  proof: by
  rwa [← LinearPMap.graph_map_snd_eq_range, toLinearPMap_graph_eq]

中文:
定理 toLinearPMap_range
  结论: (g : 子模 R (E × F))
  证明: by
  rwa [← LinearPMap.graph_map_snd_eq_range, toLinearPMap_graph_eq]

Depends on / 依赖: LinearPMap, LinearPMap.graph_map_snd_eq_range, graph_map_snd_eq_range, toLinearPMap_graph_eq
-/
theorem toLinearPMap_range (g : Submodule R (E × F))
    (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) :
    LinearMap.range g.toLinearPMap.toFun = g.map (LinearMap.snd R E F) := by
  rwa [← LinearPMap.graph_map_snd_eq_range, toLinearPMap_graph_eq]

end SubmoduleToLinearPMap

end Submodule

namespace LinearPMap

section inverse

variable [Module R F]

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : E ->ₗ.[R] F)
  body: (f.graph.map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))).toLinearPMap

中文:
定义 inverse
  签名: (f : E ->ₗ.[R] F)
  定义体: (f.graph.map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))).toLinearPMap

Depends on / 依赖: LinearEquiv, LinearEquiv.prodComm, f.graph.map, prodComm, toLinearPMap
-/
noncomputable def inverse (f : E ->ₗ.[R] F) : F ->ₗ.[R] E :=
  (f.graph.map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))).toLinearPMap

variable {f : E ->ₗ.[R] F}

/--
theorem `inverse_domain` / 定理 `inverse_domain`

English:
theorem inverse_domain
  statement: (inverse f).domain = LinearMap.range f.toFun
  proof: by
  rw [inverse]; rw [Submodule.toLinearPMap_domain]; rw [← graph_map_snd_eq_range]; rw [← LinearEquiv.fst_comp_prodComm]; rw [Submodule.map_comp]

中文:
定理 inverse_domain
  结论: (inverse f).domain = 线性映射.range f.toFun
  证明: by
  rw [inverse]; rw [Submodule.toLinearPMap_domain]; rw [← graph_map_snd_eq_range]; rw [← LinearEquiv.fst_comp_prodComm]; rw [Submodule.map_comp]

Depends on / 依赖: LinearEquiv, LinearEquiv.fst_comp_prodComm, Submodule, Submodule.map_comp, Submodule.toLinearPMap_domain, fst_comp_prodComm, graph_map_snd_eq_range, inverse, map_comp, toLinearPMap_domain
-/
theorem inverse_domain : (inverse f).domain = LinearMap.range f.toFun := by
  rw [inverse]; rw [Submodule.toLinearPMap_domain]; rw [← graph_map_snd_eq_range]; rw [← LinearEquiv.fst_comp_prodComm]; rw [Submodule.map_comp]

variable (hf : f.toFun.ker = ⊥)
include hf

/--
theorem `mem_inverse_graph_snd_eq_zero` / 定理 `mem_inverse_graph_snd_eq_zero`

English:
theorem mem_inverse_graph_snd_eq_zero
  statement: (x : F × E)
  proof: by
  rcases x with ⟨x, y⟩
  subst hv'
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.symm_prodComm,
    LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, mem_graph_iff, Prod.swap] at hv
  rcases hv with ⟨z, rfl, hz⟩
  rw [LinearMap.ker_eq_bot'] at hf
  simp [hf z hz]

中文:
定理 mem_inverse_graph_snd_eq_zero
  结论: (x : F × E)
  证明: by
  rcases x with ⟨x, y⟩
  subst hv'
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.symm_prodComm,
    LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, mem_graph_iff, Prod.swap] at hv
  rcases hv with ⟨z, rfl, hz⟩
  rw [LinearMap.ker_eq_bot'] at hf
  simp [hf z hz]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, LinearEquiv.symm_prodComm, LinearMap, LinearMap.ker_eq_bot, Prod.swap, Submodule, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, coe_coe, ker_eq_bot, map_equiv_eq_comap_symm, mem_comap, mem_graph_iff, prodComm_apply, symm_prodComm
-/
theorem mem_inverse_graph_snd_eq_zero (x : F × E)
    (hv : x in (graph f).map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E)))
    (hv' : x.fst = 0) : x.snd = 0 := by
  rcases x with ⟨x, y⟩
  subst hv'
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.symm_prodComm,
    LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, mem_graph_iff, Prod.swap] at hv
  rcases hv with ⟨z, rfl, hz⟩
  rw [LinearMap.ker_eq_bot'] at hf
  simp [hf z hz]

/--
theorem `inverse_graph` / 定理 `inverse_graph`

English:
theorem inverse_graph
  proof: by
  rw [inverse]; rw [Submodule.toLinearPMap_graph_eq _ (mem_inverse_graph_snd_eq_zero hf)]

中文:
定理 inverse_graph
  证明: by
  rw [inverse]; rw [Submodule.toLinearPMap_graph_eq _ (mem_inverse_graph_snd_eq_zero hf)]

Depends on / 依赖: Submodule, Submodule.toLinearPMap_graph_eq, inverse, mem_inverse_graph_snd_eq_zero, toLinearPMap_graph_eq
-/
theorem inverse_graph :
    (inverse f).graph = f.graph.map (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E)) := by
  rw [inverse]; rw [Submodule.toLinearPMap_graph_eq _ (mem_inverse_graph_snd_eq_zero hf)]

/--
theorem `inverse_range` / 定理 `inverse_range`

English:
theorem inverse_range
  statement: LinearMap.range (inverse f).toFun = f.domain
  proof: by
  rw [inverse]; rw [Submodule.toLinearPMap_range _ (mem_inverse_graph_snd_eq_zero hf)]; rw [← graph_map_fst_eq_domain]; rw [← LinearEquiv.snd_comp_prodComm]; rw [Submodule.map_comp]

中文:
定理 inverse_range
  结论: 线性映射.range (inverse f).toFun = f.domain
  证明: by
  rw [inverse]; rw [Submodule.toLinearPMap_range _ (mem_inverse_graph_snd_eq_zero hf)]; rw [← graph_map_fst_eq_domain]; rw [← LinearEquiv.snd_comp_prodComm]; rw [Submodule.map_comp]

Depends on / 依赖: LinearEquiv, LinearEquiv.snd_comp_prodComm, Submodule, Submodule.map_comp, Submodule.toLinearPMap_range, graph_map_fst_eq_domain, inverse, map_comp, mem_inverse_graph_snd_eq_zero, snd_comp_prodComm, toLinearPMap_range
-/
theorem inverse_range : LinearMap.range (inverse f).toFun = f.domain := by
  rw [inverse]; rw [Submodule.toLinearPMap_range _ (mem_inverse_graph_snd_eq_zero hf)]; rw [← graph_map_fst_eq_domain]; rw [← LinearEquiv.snd_comp_prodComm]; rw [Submodule.map_comp]

/--
theorem `mem_inverse_graph` / 定理 `mem_inverse_graph`

English:
theorem mem_inverse_graph
  given: (x : f.domain)
  statement: (f x, (x : E)) in (inverse f).graph
  proof: by
  simp only [inverse_graph hf, Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  exact ⟨(x : E), f x, ⟨x.2, Eq.refl _⟩, Eq.refl _, Eq.refl _⟩

中文:
定理 mem_inverse_graph
  条件: (x : f.domain)
  结论: (f x, (x : E)) in (inverse f).graph
  证明: by
  simp only [inverse_graph hf, Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  exact ⟨(x : E), f x, ⟨x.2, Eq.refl _⟩, Eq.refl _, Eq.refl _⟩

Depends on / 依赖: Eq.refl, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.exists, Prod.mk.injEq, Prod.swap_prod_mk, Submodule, Submodule.mem_map, Subtype, Subtype.exists, coe_coe, exists_and_left, exists_eq_left, inverse_graph, mem_graph_iff, mem_map, prodComm_apply, swap_prod_mk
-/
theorem mem_inverse_graph (x : f.domain) : (f x, (x : E)) in (inverse f).graph := by
  simp only [inverse_graph hf, Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  exact ⟨(x : E), f x, ⟨x.2, Eq.refl _⟩, Eq.refl _, Eq.refl _⟩

/--
theorem `inverse_apply_eq` / 定理 `inverse_apply_eq`

English:
theorem inverse_apply_eq
  given: {y : (inverse f).domain} {x : f.domain} (hxy : f x = y)
  proof: by
  have := mem_inverse_graph hf x
  grind

中文:
定理 inverse_apply_eq
  条件: {y : (inverse f).domain} {x : f.domain} (hxy : f x = y)
  证明: by
  have := mem_inverse_graph hf x
  grind

Depends on / 依赖: mem_inverse_graph
-/
theorem inverse_apply_eq {y : (inverse f).domain} {x : f.domain} (hxy : f x = y) :
    (inverse f) y = x := by
  have := mem_inverse_graph hf x
  grind

end inverse

end LinearPMap
