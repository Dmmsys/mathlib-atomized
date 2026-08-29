/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Maps on modules and ideals

Main definitions include `Ideal.map`, `Ideal.comap`, `RingHom.ker`, `Module.annihilator`
and `Submodule.annihilator`.
-/

@[expose] public section

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`
  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open scoped Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]
variable [FunLike F R S]
variable (f : F)
variable {I J : Ideal R} {K L : Ideal S}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (I : Ideal R)
  body: span (f '' I)

中文:
定义 map
  签名: (I : 理想 R)
  定义体: span (f '' I)
-/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: [RingHomClass F R S] (I : Ideal S)
  body: f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

@[simp]

中文:
定义 comap
  签名: [环态射类 F R S] (I : 理想 S)
  定义体: f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

@[simp]
-/
def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: [RingHomClass F R S] (I : Ideal S)
  statement: (comap f I : Set R) = f ⁻¹' I
  proof: rfl

中文:
定理 coe_comap
  条件: [环态射类 F R S] (I : 理想 S)
  结论: (comap f I : 集合 R) = f ⁻¹' I
  证明: rfl
-/
theorem coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f I : Set R) = f ⁻¹' I := rfl

/--
lemma `comap_coe` / 引理 `comap_coe`

English:
lemma comap_coe
  given: [RingHomClass F R S] (I : Ideal S)
  statement: I.comap (f : R ->+* S) = I.comap f
  proof: rfl

中文:
引理 comap_coe
  条件: [环态射类 F R S] (I : 理想 S)
  结论: I.comap (f : R ->+* S) = I.comap f
  证明: rfl
-/
lemma comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap (f : R ->+* S) = I.comap f := rfl

/--
lemma `map_coe` / 引理 `map_coe`

English:
lemma map_coe
  given: [RingHomClass F R S] (I : Ideal R)
  statement: I.map (f : R ->+* S) = I.map f
  proof: rfl

中文:
引理 map_coe
  条件: [环态射类 F R S] (I : 理想 R)
  结论: I.map (f : R ->+* S) = I.map f
  证明: rfl
-/
lemma map_coe [RingHomClass F R S] (I : Ideal R) : I.map (f : R ->+* S) = I.map f := rfl

variable {f}

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (h : I <= J)
  statement: map f I <= map f J
  proof: span_mono Set.image_mono h

中文:
定理 map_mono
  条件: (h : I <= J)
  结论: map f I <= map f J
  证明: span_mono Set.image_mono h

Depends on / 依赖: Set.image_mono, image_mono, span_mono
-/
theorem map_mono (h : I <= J) : map f I <= map f J :=
span_mono Set.image_mono h

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : F) {I : Ideal R} {x : R} (h : x in I)
  statement: f x in map f I
  proof: subset_span ⟨x, h, rfl⟩

中文:
定理 mem_map_of_mem
  条件: (f : F) {I : 理想 R} {x : R} (h : x in I)
  结论: f x in map f I
  证明: subset_span ⟨x, h, rfl⟩

Depends on / 依赖: subset_span
-/
theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x in I) : f x in map f I :=
  subset_span ⟨x, h, rfl⟩

/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : F) (I : Ideal R) (x : I)
  statement: f x in I.map f
  proof: mem_map_of_mem f x.2

中文:
定理 apply_coe_mem_map
  条件: (f : F) (I : 理想 R) (x : I)
  结论: f x in I.map f
  证明: mem_map_of_mem f x.2

Depends on / 依赖: mem_map_of_mem
-/
theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x in I.map f :=
  mem_map_of_mem f x.2

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: [RingHomClass F R S]
  statement: map f I <= K ↔ I <= comap f K
  proof: span_le.trans Set.image_subset_iff

@[simp]

中文:
定理 map_le_iff_le_comap
  条件: [环态射类 F R S]
  结论: map f I <= K ↔ I <= comap f K
  证明: span_le.trans Set.image_subset_iff

@[simp]

Depends on / 依赖: Set.image_subset_iff, image_subset_iff, span_le, span_le.trans
-/
theorem map_le_iff_le_comap [RingHomClass F R S] : map f I <= K ↔ I <= comap f K :=
  span_le.trans Set.image_subset_iff

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: [RingHomClass F R S] {x}
  statement: x in comap f K ↔ f x in K
  proof: Iff.rfl

@[gcongr]

中文:
定理 mem_comap
  条件: [环态射类 F R S] {x}
  结论: x in comap f K ↔ f x in K
  证明: Iff.rfl

@[gcongr]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f x in K :=
  Iff.rfl

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: [RingHomClass F R S] (h : K <= L)
  statement: comap f K <= comap f L
  proof: Set.preimage_mono fun _ hx => h hx

中文:
定理 comap_mono
  条件: [环态射类 F R S] (h : K <= L)
  结论: comap f K <= comap f L
  证明: Set.preimage_mono fun _ hx => h hx

Depends on / 依赖: Set.preimage_mono, preimage_mono
-/
theorem comap_mono [RingHomClass F R S] (h : K <= L) : comap f K <= comap f L :=
  Set.preimage_mono fun _ hx => h hx

variable (f)

/--
theorem `comap_ne_top` / 定理 `comap_ne_top`

English:
theorem comap_ne_top
  given: [RingHomClass F R S] (hK : K != ⊤)
  statement: comap f K != ⊤
  proof: (ne_top_iff_one _).2 by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK

中文:
定理 comap_ne_top
  条件: [环态射类 F R S] (hK : K != ⊤)
  结论: comap f K != ⊤
  证明: (ne_top_iff_one _).2 by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK

Depends on / 依赖: map_one, mem_comap, ne_top_iff_one
-/
theorem comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : comap f K != ⊤ :=
(ne_top_iff_one _).2 by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK

/--
lemma `exists_ideal_comap_le_prime` / 引理 `exists_ideal_comap_le_prime`

English:
lemma exists_ideal_comap_le_prime
  statement: {S} [CommSemiring S] [FunLike F R S] [RingHomClass F R S]
  proof: have ⟨Q, hQ, hIQ, disj⟩ := I.exists_le_prime_disjoint (P.primeCompl.map f)
    Set.disjoint_left.mpr fun _ => by rintro hI ⟨r, hp, rfl⟩; exact hp (le hI)
  ⟨Q, hIQ, hQ, fun r hp' => of_not_not fun hp => Set.disjoint_left.mp disj hp' ⟨_, hp, rfl⟩⟩

中文:
引理 存在_ideal_comap_le_prime
  结论: {S} [交换半环 S] [函数状 F R S] [环态射类 F R S]
  证明: have ⟨Q, hQ, hIQ, disj⟩ := I.exists_le_prime_disjoint (P.primeCompl.map f)
    Set.disjoint_left.mpr fun _ => by rintro hI ⟨r, hp, rfl⟩; exact hp (le hI)
  ⟨Q, hIQ, hQ, fun r hp' => of_not_not fun hp => Set.disjoint_left.mp disj hp' ⟨_, hp, rfl⟩⟩

Depends on / 依赖: I.exists_le_prime_disjoint, P.primeCompl.map, Set.disjoint_left.mp, Set.disjoint_left.mpr, disjoint_left, exists_le_prime_disjoint, of_not_not, primeCompl
-/
lemma exists_ideal_comap_le_prime {S} [CommSemiring S] [FunLike F R S] [RingHomClass F R S]
    {f : F} (P : Ideal R) [P.IsPrime] (I : Ideal S) (le : I.comap f <= P) :
    exists Q >= I, Q.IsPrime ∧ Q.comap f <= P :=
have ⟨Q, hQ, hIQ, disj⟩ := I.exists_le_prime_disjoint (P.primeCompl.map f)
    Set.disjoint_left.mpr fun _ => by rintro hI ⟨r, hp, rfl⟩; exact hp (le hI)
  ⟨Q, hIQ, hQ, fun r hp' => of_not_not fun hp => Set.disjoint_left.mp disj hp' ⟨_, hp, rfl⟩⟩

variable {G : Type*} [FunLike G S R]

/--
theorem `map_le_comap_of_inv_on` / 定理 `map_le_comap_of_inv_on`

English:
theorem map_le_comap_of_inv_on
  statement: [RingHomClass G S R] (g : G) (I : Ideal R)
  proof: by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe]; rw [mem_comap]; rw [hf hx]
  exact hx

中文:
定理 map_le_comap_of_inv_on
  结论: [环态射类 G S R] (g : G) (I : 理想 R)
  证明: by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe]; rw [mem_comap]; rw [hf hx]
  exact hx

Depends on / 依赖: Ideal.span_le, SetLike, SetLike.mem_coe, mem_coe, mem_comap, span_le
-/
theorem map_le_comap_of_inv_on [RingHomClass G S R] (g : G) (I : Ideal R)
    (hf : Set.LeftInvOn g f I) :
    I.map f <= I.comap g := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe]; rw [mem_comap]; rw [hf hx]
  exact hx

/--
theorem `comap_le_map_of_inv_on` / 定理 `comap_le_map_of_inv_on`

English:
theorem comap_le_map_of_inv_on
  statement: [RingHomClass F R S] (g : G) (I : Ideal S)
  proof: fun x (hx : f x in I) => hf hx ▸ Ideal.mem_map_of_mem g hx

中文:
定理 comap_le_map_of_inv_on
  结论: [环态射类 F R S] (g : G) (I : 理想 S)
  证明: fun x (hx : f x in I) => hf hx ▸ Ideal.mem_map_of_mem g hx

Depends on / 依赖: Ideal.mem_map_of_mem, mem_map_of_mem
-/
theorem comap_le_map_of_inv_on [RingHomClass F R S] (g : G) (I : Ideal S)
    (hf : Set.LeftInvOn g f (f ⁻¹' I)) :
    I.comap f <= I.map g :=
  fun x (hx : f x in I) => hf hx ▸ Ideal.mem_map_of_mem g hx

/--
theorem `map_le_comap_of_inverse` / 定理 `map_le_comap_of_inverse`

English:
theorem map_le_comap_of_inverse
  statement: [RingHomClass G S R] (g : G) (I : Ideal R)
  proof: map_le_comap_of_inv_on _ _ _ h.leftInvOn _

中文:
定理 map_le_comap_of_inverse
  结论: [环态射类 G S R] (g : G) (I : 理想 R)
  证明: map_le_comap_of_inv_on _ _ _ h.leftInvOn _

Depends on / 依赖: h.leftInvOn, leftInvOn, map_le_comap_of_inv_on
-/
theorem map_le_comap_of_inverse [RingHomClass G S R] (g : G) (I : Ideal R)
    (h : Function.LeftInverse g f) :
    I.map f <= I.comap g :=
map_le_comap_of_inv_on _ _ _ h.leftInvOn _

/--
theorem `eq_bot_of_comap_eq_bot'` / 定理 `eq_bot_of_comap_eq_bot'`

English:
theorem eq_bot_of_comap_eq_bot'
  statement: {f : R ->+* S} (hf : Function.Surjective f)
  proof: by
  ext x
  obtain ⟨y, hy⟩ := hf x
  aesop (add norm [Submodule.eq_bot_iff])

中文:
定理 eq_bot_of_comap_eq_bot'
  结论: {f : R ->+* S} (hf : 函数.满射 f)
  证明: by
  ext x
  obtain ⟨y, hy⟩ := hf x
  aesop (add norm [Submodule.eq_bot_iff])

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, eq_bot_iff
-/
theorem eq_bot_of_comap_eq_bot' {f : R ->+* S} (hf : Function.Surjective f)
    {I : Ideal S} (h : I.comap f = ⊥) :
    I = ⊥ := by
  ext x
  obtain ⟨y, hy⟩ := hf x
  aesop (add norm [Submodule.eq_bot_iff])

variable [RingHomClass F R S]

instance (priority := low) [K.IsTwoSided] : (comap f K).IsTwoSided :=
  ⟨fun b ha => by rw [mem_comap, map_mul]; exact mul_mem_right _ _ ha⟩

/--
theorem `comap_le_map_of_inverse` / 定理 `comap_le_map_of_inverse`

English:
theorem comap_le_map_of_inverse
  given: (g : G) (I : Ideal S) (h : Function.LeftInverse g f)
  proof: comap_le_map_of_inv_on _ _ _ h.leftInvOn _

中文:
定理 comap_le_map_of_inverse
  条件: (g : G) (I : 理想 S) (h : 函数.左逆 g f)
  证明: comap_le_map_of_inv_on _ _ _ h.leftInvOn _

Depends on / 依赖: comap_le_map_of_inv_on, h.leftInvOn, leftInvOn
-/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) :
    I.comap f <= I.map g :=
comap_le_map_of_inv_on _ _ _ h.leftInvOn _

/--
Instance `IsPrime.comap` / 实例 `IsPrime.comap`

English:
instance IsPrime.comap
  signature: [hK : K.IsPrime]
  body: ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩

中文:
实例 是素.comap
  签名: [hK : K.是素]
  定义体: ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩

Depends on / 依赖: comap_ne_top, map_mul, mem_comap
-/
instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩

variable (I J K L)

/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  statement: map f ⊤ = ⊤
  proof: (eq_top_iff_one _).2 subset_span ⟨1, trivial, map_one f⟩

中文:
定理 map_top
  结论: map f ⊤ = ⊤
  证明: (eq_top_iff_one _).2 subset_span ⟨1, trivial, map_one f⟩

Depends on / 依赖: eq_top_iff_one, map_one, subset_span
-/
theorem map_top : map f ⊤ = ⊤ :=
(eq_top_iff_one _).2 subset_span ⟨1, trivial, map_one f⟩

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  statement: GaloisConnection (Ideal.map f) (Ideal.comap f)
  proof: fun _ _ =>
  Ideal.map_le_iff_le_comap

@[simp]

中文:
定理 gc_map_comap
  结论: GaloisConnection (理想.map f) (理想.comap f)
  证明: fun _ _ =>
  Ideal.map_le_iff_le_comap

@[simp]
-/
theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun _ _ =>
  Ideal.map_le_iff_le_comap

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: I.comap (RingHom.id R) = I
  proof: Ideal.ext fun _ => Iff.rfl

@[simp]

中文:
定理 comap_id
  结论: I.comap (环态射.id R) = I
  证明: Ideal.ext fun _ => Iff.rfl

@[simp]

Depends on / 依赖: Ideal.ext, Iff.rfl
-/
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl

@[simp]
/--
lemma `comap_idₐ` / 引理 `comap_idₐ`

English:
lemma comap_idₐ
  given: {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S)
  proof: I.comap_id

@[simp]

中文:
引理 comap_idₐ
  条件: {R S : 类型} [交换半环 R] [半环 S] [代数 R S] (I : 理想 S)
  证明: I.comap_id

@[simp]

Depends on / 依赖: I.comap_id, comap_id
-/
lemma comap_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.comap (AlgHom.id R S) I = I :=
  I.comap_id

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: I.map (RingHom.id R) = I
  proof: (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

@[simp]

中文:
定理 map_id
  结论: I.map (环态射.id R) = I
  证明: (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

@[simp]

Depends on / 依赖: GaloisConnection, GaloisConnection.id, RingHom, RingHom.id, comap_id, gc_map_comap, l_unique
-/
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

@[simp]
/--
lemma `map_idₐ` / 引理 `map_idₐ`

English:
lemma map_idₐ
  given: {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S)
  proof: I.map_id

中文:
引理 map_idₐ
  条件: {R S : 类型} [交换半环 R] [半环 S] [代数 R S] (I : 理想 S)
  证明: I.map_id

Depends on / 依赖: I.map_id, map_id
-/
lemma map_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.map (AlgHom.id R S) I = I :=
  I.map_id

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: {T : Type*} [Semiring T] {I : Ideal T} (f : R ->+* S) (g : S ->+* T)
  proof: rfl

中文:
定理 comap_comap
  条件: {T : 类型} [半环 T] {I : 理想 T} (f : R ->+* S) (g : S ->+* T)
  证明: rfl
-/
theorem comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R ->+* S) (g : S ->+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl

/--
lemma `comap_comapₐ` / 引理 `comap_comapₐ`

English:
lemma comap_comapₐ
  statement: {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
  proof: I.comap_comap f.toRingHom g.toRingHom

中文:
引理 comap_comapₐ
  结论: {R A B C : 类型} [交换半环 R] [半环 A] [代数 R A] [半环 B]
  证明: I.comap_comap f.toRingHom g.toRingHom

Depends on / 依赖: I.comap_comap, comap_comap, f.toRingHom, g.toRingHom, toRingHom
-/
lemma comap_comapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal C} (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  I.comap_comap f.toRingHom g.toRingHom

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+* S) (g : S ->+* T)
  proof: ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _

中文:
定理 map_map
  条件: {T : 类型} [半环 T] {I : 理想 R} (f : R ->+* S) (g : S ->+* T)
  证明: ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _

Depends on / 依赖: comap_comap, compose, g.comp, gc_map_comap, l_unique
-/
theorem map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+* S) (g : S ->+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _

/--
lemma `map_mapₐ` / 引理 `map_mapₐ`

English:
lemma map_mapₐ
  statement: {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
  proof: I.map_map f.toRingHom g.toRingHom

中文:
引理 map_mapₐ
  结论: {R A B C : 类型} [交换半环 R] [半环 A] [代数 R A] [半环 B]
  证明: I.map_map f.toRingHom g.toRingHom

Depends on / 依赖: I.map_map, f.toRingHom, g.toRingHom, map_map, toRingHom
-/
lemma map_mapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal A} (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) :
    (I.map f).map g = I.map (g.comp f) :=
  I.map_map f.toRingHom g.toRingHom

/--
theorem `map_span` / 定理 `map_span`

English:
theorem map_span
  given: (s : Set R)
  statement: map f (span s) = span (f '' s)
  proof: by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span

中文:
定理 map_span
  条件: (s : 集合 R)
  结论: map f (span s) = span (f '' s)
  证明: by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span

Depends on / 依赖: Set.image_subset_iff, Submodule, Submodule.span_eq_of_le, coe_comap, image_subset_iff, map_le_iff_le_comap, mem_map_of_mem, span_eq_of_le, span_le, subset_span
-/
theorem map_span (s : Set R) : map f (span s) = span (f '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span

variable {f I J K L}

/--
theorem `map_le_of_le_comap` / 定理 `map_le_of_le_comap`

English:
theorem map_le_of_le_comap
  statement: I <= K.comap f -> I.map f <= K
  proof: (gc_map_comap f).l_le

中文:
定理 map_le_of_le_comap
  结论: I <= K.comap f -> I.map f <= K
  证明: (gc_map_comap f).l_le

Depends on / 依赖: gc_map_comap, l_le
-/
theorem map_le_of_le_comap : I <= K.comap f -> I.map f <= K :=
  (gc_map_comap f).l_le

/--
theorem `le_comap_of_map_le` / 定理 `le_comap_of_map_le`

English:
theorem le_comap_of_map_le
  statement: I.map f <= K -> I <= K.comap f
  proof: (gc_map_comap f).le_u

中文:
定理 le_comap_of_map_le
  结论: I.map f <= K -> I <= K.comap f
  证明: (gc_map_comap f).le_u

Depends on / 依赖: gc_map_comap, le_u
-/
theorem le_comap_of_map_le : I.map f <= K -> I <= K.comap f :=
  (gc_map_comap f).le_u

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  statement: I <= (I.map f).comap f
  proof: (gc_map_comap f).le_u_l _

中文:
定理 le_comap_map
  结论: I <= (I.map f).comap f
  证明: (gc_map_comap f).le_u_l _

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map : I <= (I.map f).comap f :=
  (gc_map_comap f).le_u_l _

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  statement: (K.comap f).map f <= K
  proof: (gc_map_comap f).l_u_le _

@[simp]

中文:
定理 map_comap_le
  结论: (K.comap f).map f <= K
  证明: (gc_map_comap f).l_u_le _

@[simp]

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le : (K.comap f).map f <= K :=
  (gc_map_comap f).l_u_le _

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  statement: (⊤ : Ideal S).comap f = ⊤
  proof: (gc_map_comap f).u_top

@[simp]

中文:
定理 comap_top
  结论: (⊤ : 理想 S).comap f = ⊤
  证明: (gc_map_comap f).u_top

@[simp]

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
/--
theorem `comap_eq_top_iff` / 定理 `comap_eq_top_iff`

English:
theorem comap_eq_top_iff
  given: {I : Ideal S}
  statement: I.comap f = ⊤ ↔ I = ⊤
  proof: ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩

@[simp]

中文:
定理 comap_eq_top_iff
  条件: {I : 理想 S}
  结论: I.comap f = ⊤ ↔ I = ⊤
  证明: ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩

@[simp]

Depends on / 依赖: I.comap, I.eq_top_iff_one.mpr, comap_top, eq_top_iff_one, eq_top_iff_one.mp, map_one, mem_comap, mem_comap.mp
-/
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  statement: (⊥ : Ideal R).map f = ⊥
  proof: (gc_map_comap f).l_bot

中文:
定理 map_bot
  结论: (⊥ : 理想 R).map f = ⊥
  证明: (gc_map_comap f).l_bot

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot

/--
theorem `ne_bot_of_map_ne_bot` / 定理 `ne_bot_of_map_ne_bot`

English:
theorem ne_bot_of_map_ne_bot
  given: (hI : map f I != ⊥)
  statement: I != ⊥
  proof: fun h => hI (Eq.mpr (congrArg (fun I => map f I = ⊥) h) map_bot)

中文:
定理 ne_bot_of_map_ne_bot
  条件: (hI : map f I != ⊥)
  结论: I != ⊥
  证明: fun h => hI (Eq.mpr (congrArg (fun I => map f I = ⊥) h) map_bot)

Depends on / 依赖: Eq.mpr, map_bot
-/
theorem ne_bot_of_map_ne_bot (hI : map f I != ⊥) : I != ⊥ :=
  fun h => hI (Eq.mpr (congrArg (fun I => map f I = ⊥) h) map_bot)

variable (f I J K L)

@[simp]
/--
theorem `map_comap_map` / 定理 `map_comap_map`

English:
theorem map_comap_map
  statement: ((I.map f).comap f).map f = I.map f
  proof: (gc_map_comap f).l_u_l_eq_l I

@[simp]

中文:
定理 map_comap_map
  结论: ((I.map f).comap f).map f = I.map f
  证明: (gc_map_comap f).l_u_l_eq_l I

@[simp]

Depends on / 依赖: gc_map_comap, l_u_l_eq_l
-/
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I

@[simp]
/--
theorem `comap_map_comap` / 定理 `comap_map_comap`

English:
theorem comap_map_comap
  statement: ((K.comap f).map f).comap f = K.comap f
  proof: (gc_map_comap f).u_l_u_eq_u K

中文:
定理 comap_map_comap
  结论: ((K.comap f).map f).comap f = K.comap f
  证明: (gc_map_comap f).u_l_u_eq_u K

Depends on / 依赖: gc_map_comap, u_l_u_eq_u
-/
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: (I ⊔ J).map f = I.map f ⊔ J.map f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

中文:
定理 map_sup
  结论: (I ⊔ J).map f = I.map f ⊔ J.map f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

Depends on / 依赖: GaloisConnection, gc_map_comap, l_sup
-/
theorem map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  statement: comap f (K ⊓ L) = comap f K ⊓ comap f L
  proof: rfl

中文:
定理 comap_inf
  结论: comap f (K ⊓ L) = comap f K ⊓ comap f L
  证明: rfl
-/
theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl

variable {ι : Sort*}

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: (K : ι -> Ideal R)
  statement: (iSup K).map f = ⨆ i, (K i).map f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

中文:
定理 map_iSup
  条件: (K : ι -> 理想 R)
  结论: (iSup K).map f = ⨆ i, (K i).map f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

Depends on / 依赖: GaloisConnection, gc_map_comap, l_iSup
-/
theorem map_iSup (K : ι -> Ideal R) : (iSup K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: (K : ι -> Ideal S)
  statement: (iInf K).comap f = ⨅ i, (K i).comap f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

中文:
定理 comap_iInf
  条件: (K : ι -> 理想 S)
  结论: (iInf K).comap f = ⨅ i, (K i).comap f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

Depends on / 依赖: GaloisConnection, gc_map_comap, u_iInf
-/
theorem comap_iInf (K : ι -> Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

/--
theorem `comap_finsetInf` / 定理 `comap_finsetInf`

English:
theorem comap_finsetInf
  given: {ι : Type*} (s : Finset ι) (K : ι -> Ideal S)
  proof: by
  simp [Finset.inf_eq_iInf, comap_iInf]

中文:
定理 comap_finsetInf
  条件: {ι : 类型} (s : 有限集 ι) (K : ι -> 理想 S)
  证明: by
  simp [Finset.inf_eq_iInf, comap_iInf]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, comap_iInf, inf_eq_iInf
-/
theorem comap_finsetInf {ι : Type*} (s : Finset ι) (K : ι -> Ideal S) :
    (s.inf K).comap f = s.inf fun i => (K i).comap f := by
  simp [Finset.inf_eq_iInf, comap_iInf]

/--
theorem `map_sSup` / 定理 `map_sSup`

English:
theorem map_sSup
  given: (s : Set (Ideal R))
  statement: (sSup s).map f = ⨆ I in s, (I : Ideal R).map f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup

中文:
定理 map_sSup
  条件: (s : 集合 (理想 R))
  结论: (sSup s).map f = ⨆ I in s, (I : 理想 R).map f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup

Depends on / 依赖: GaloisConnection, gc_map_comap, l_sSup
-/
theorem map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I in s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup

/--
theorem `comap_sInf` / 定理 `comap_sInf`

English:
theorem comap_sInf
  given: (s : Set (Ideal S))
  statement: (sInf s).comap f = ⨅ I in s, (I : Ideal S).comap f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf

中文:
定理 comap_sInf
  条件: (s : 集合 (理想 S))
  结论: (sInf s).comap f = ⨅ I in s, (I : 理想 S).comap f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf

Depends on / 依赖: GaloisConnection, gc_map_comap, u_sInf
-/
theorem comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I in s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf

/--
theorem `comap_sInf'` / 定理 `comap_sInf'`

English:
theorem comap_sInf'
  given: (s : Set (Ideal S))
  statement: (sInf s).comap f = ⨅ I in comap f '' s, I
  proof: _root_.trans (comap_sInf f s) (by rw [iInf_image])

中文:
定理 comap_sInf'
  条件: (s : 集合 (理想 S))
  结论: (sInf s).comap f = ⨅ I in comap f '' s, I
  证明: _root_.trans (comap_sInf f s) (by rw [iInf_image])

Depends on / 依赖: _root_, _root_.trans, comap_sInf, iInf_image
-/
theorem comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I in comap f '' s, I :=
  _root_.trans (comap_sInf f s) (by rw [iInf_image])

/--
theorem `comap_isPrime` / 定理 `comap_isPrime`

English:
theorem comap_isPrime
  given: [H : IsPrime K]
  statement: IsPrime (comap f K)
  proof: H.comap f

中文:
定理 comap_isPrime
  条件: [H : 是素 K]
  结论: 是素 (comap f K)
  证明: H.comap f

Depends on / 依赖: H.comap
-/
theorem comap_isPrime [H : IsPrime K] : IsPrime (comap f K) :=
  H.comap f

variable {I J K L}

/--
theorem `map_inf_le` / 定理 `map_inf_le`

English:
theorem map_inf_le
  statement: map f (I ⊓ J) <= map f I ⊓ map f J
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _

中文:
定理 map_inf_le
  结论: map f (I ⊓ J) <= map f I ⊓ map f J
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _

Depends on / 依赖: GaloisConnection, gc_map_comap, map_inf_le, monotone_l, monotone_l.map_inf_le
-/
theorem map_inf_le : map f (I ⊓ J) <= map f I ⊓ map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _

/--
theorem `le_comap_sup` / 定理 `le_comap_sup`

English:
theorem le_comap_sup
  statement: comap f K ⊔ comap f L <= comap f (K ⊔ L)
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

中文:
定理 le_comap_sup
  结论: comap f K ⊔ comap f L <= comap f (K ⊔ L)
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

Depends on / 依赖: GaloisConnection, gc_map_comap, le_map_sup, monotone_u, monotone_u.le_map_sup
-/
theorem le_comap_sup : comap f K ⊔ comap f L <= comap f (K ⊔ L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

-- TODO: Should these be simp lemmas?
/--
theorem `_root_.element_smul_restrictScalars` / 定理 `_root_.element_smul_restrictScalars`

English:
theorem _root_.element_smul_restrictScalars
  statement: {R S M}
  proof: SetLike.coe_injective (congrArg (· '' _) (funext (algebraMap_smul S r)))

中文:
定理 _root_.element_smul_restrictScalars
  结论: {R S M}
  证明: SetLike.coe_injective (congrArg (· '' _) (funext (algebraMap_smul S r)))

Depends on / 依赖: SetLike, SetLike.coe_injective, algebraMap_smul, coe_injective
-/
theorem _root_.element_smul_restrictScalars {R S M}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (r : R) (N : Submodule S M) :
    (algebraMap R S r • N).restrictScalars R = r • N.restrictScalars R :=
  SetLike.coe_injective (congrArg (· '' _) (funext (algebraMap_smul S r)))

/--
theorem `smul_restrictScalars` / 定理 `smul_restrictScalars`

English:
theorem smul_restrictScalars
  statement: {R S M} [CommSemiring R] [CommSemiring S]
  proof: by
  simp_rw [map, Submodule.span_smul_eq, ← Submodule.coe_set_smul,
    Submodule.set_smul_eq_iSup, ← element_smul_restrictScalars, iSup_image]
  exact map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _

@[simp]

中文:
定理 smul_restrictScalars
  结论: {R S M} [交换半环 R] [交换半环 S]
  证明: by
  simp_rw [map, Submodule.span_smul_eq, ← Submodule.coe_set_smul,
    Submodule.set_smul_eq_iSup, ← element_smul_restrictScalars, iSup_image]
  exact map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _

@[simp]

Depends on / 依赖: Submodule, Submodule.coe_set_smul, Submodule.restrictScalarsLatticeHom, Submodule.set_smul_eq_iSup, Submodule.span_smul_eq, coe_set_smul, element_smul_restrictScalars, iSup_image, restrictScalarsLatticeHom, set_smul_eq_iSup, simp_rw, span_smul_eq
-/
theorem smul_restrictScalars {R S M} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (N : Submodule S M) :
    (I.map (algebraMap R S) • N).restrictScalars R = I • N.restrictScalars R := by
  simp_rw [map, Submodule.span_smul_eq, ← Submodule.coe_set_smul,
    Submodule.set_smul_eq_iSup, ← element_smul_restrictScalars, iSup_image]
  exact map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _

@[simp]
/--
theorem `smul_top_eq_map` / 定理 `smul_top_eq_map`

English:
theorem smul_top_eq_map
  statement: {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  proof: Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm
congrArg _ Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)

@[simp]

中文:
定理 smul_top_eq_map
  结论: {R S : 类型} [交换半环 R] [交换半环 S] [代数 R S]
  证明: Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm
congrArg _ Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)

@[simp]

Depends on / 依赖: Eq.trans, Ideal.mul_top, Ideal.smul_eq_mul, mul_top, smul_eq_mul, smul_restrictScalars
-/
theorem smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R :=
Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm
congrArg _ Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  statement: {R S : Type*} [Semiring R] [Semiring S] [Module R S]
  proof: rfl

中文:
定理 coe_restrictScalars
  结论: {R S : 类型} [半环 R] [半环 S] [模 R S]
  证明: rfl
-/
theorem coe_restrictScalars {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I :=
  rfl

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp]
/--
theorem `restrictScalars_mul` / 定理 `restrictScalars_mul`

English:
theorem restrictScalars_mul
  statement: {R S : Type*} [Semiring R] [Semiring S] [Module R S]
  proof: rfl

中文:
定理 restrictScalars_mul
  结论: {R S : 类型} [半环 R] [半环 S] [模 R S]
  证明: rfl
-/
theorem restrictScalars_mul {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I J : Ideal S) :
    (I * J).restrictScalars R = I.restrictScalars R * J.restrictScalars R :=
  rfl

section Surjective

section

variable (hf : Function.Surjective f)
include hf

open Function

/--
theorem `map_comap_of_surjective` / 定理 `map_comap_of_surjective`

English:
theorem map_comap_of_surjective
  given: (I : Ideal S)
  statement: map f (comap f I) = I
  proof: le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r in I from hfrs.symm ▸ hsi)

中文:
定理 map_comap_of_surjective
  条件: (I : 理想 S)
  结论: map f (comap f I) = I
  证明: le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r in I from hfrs.symm ▸ hsi)

Depends on / 依赖: hfrs.symm, le_antisymm, le_rfl, map_le_iff_le_comap, mem_map_of_mem
-/
theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r in I from hfrs.symm ▸ hsi)

/--
Definition of `giMapComap` / `giMapComap` 的定义

English:
definition giMapComap
  signature: : GaloisInsertion (map f) (comap f)
  body: GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)

中文:
定义 giMapComap
  签名: : Galois嵌入 (map f) (comap f)
  定义体: GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)

Depends on / 依赖: GaloisInsertion, GaloisInsertion.monotoneIntro, gc_map_comap, le_comap_map, map_comap_of_surjective, monotoneIntro, monotone_l, monotone_u
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)

/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  statement: Surjective (map f)
  proof: (giMapComap f hf).l_surjective

中文:
定理 map_surjective_of_surjective
  结论: 满射 (map f)
  证明: (giMapComap f hf).l_surjective

Depends on / 依赖: giMapComap, l_surjective
-/
theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective

/--
theorem `comap_injective_of_surjective` / 定理 `comap_injective_of_surjective`

English:
theorem comap_injective_of_surjective
  statement: Injective (comap f)
  proof: (giMapComap f hf).u_injective

中文:
定理 comap_injective_of_surjective
  结论: 单射 (comap f)
  证明: (giMapComap f hf).u_injective

Depends on / 依赖: giMapComap, u_injective
-/
theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective

/--
theorem `map_sup_comap_of_surjective` / 定理 `map_sup_comap_of_surjective`

English:
theorem map_sup_comap_of_surjective
  given: (I J : Ideal S)
  statement: (I.comap f ⊔ J.comap f).map f = I ⊔ J
  proof: (giMapComap f hf).l_sup_u _ _

中文:
定理 map_sup_comap_of_surjective
  条件: (I J : 理想 S)
  结论: (I.comap f ⊔ J.comap f).map f = I ⊔ J
  证明: (giMapComap f hf).l_sup_u _ _

Depends on / 依赖: giMapComap, l_sup_u
-/
theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
  (giMapComap f hf).l_sup_u _ _

/--
theorem `map_iSup_comap_of_surjective` / 定理 `map_iSup_comap_of_surjective`

English:
theorem map_iSup_comap_of_surjective
  given: (K : ι -> Ideal S)
  statement: (⨆ i, (K i).comap f).map f = iSup K
  proof: (giMapComap f hf).l_iSup_u _

中文:
定理 map_iSup_comap_of_surjective
  条件: (K : ι -> 理想 S)
  结论: (⨆ i, (K i).comap f).map f = iSup K
  证明: (giMapComap f hf).l_iSup_u _

Depends on / 依赖: giMapComap, l_iSup_u
-/
theorem map_iSup_comap_of_surjective (K : ι -> Ideal S) : (⨆ i, (K i).comap f).map f = iSup K :=
  (giMapComap f hf).l_iSup_u _

/--
theorem `map_inf_comap_of_surjective` / 定理 `map_inf_comap_of_surjective`

English:
theorem map_inf_comap_of_surjective
  given: (I J : Ideal S)
  statement: (I.comap f ⊓ J.comap f).map f = I ⊓ J
  proof: (giMapComap f hf).l_inf_u _ _

中文:
定理 map_inf_comap_of_surjective
  条件: (I J : 理想 S)
  结论: (I.comap f ⊓ J.comap f).map f = I ⊓ J
  证明: (giMapComap f hf).l_inf_u _ _

Depends on / 依赖: giMapComap, l_inf_u
-/
theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
  (giMapComap f hf).l_inf_u _ _

/--
theorem `map_iInf_comap_of_surjective` / 定理 `map_iInf_comap_of_surjective`

English:
theorem map_iInf_comap_of_surjective
  given: (K : ι -> Ideal S)
  statement: (⨅ i, (K i).comap f).map f = iInf K
  proof: (giMapComap f hf).l_iInf_u _

中文:
定理 map_iInf_comap_of_surjective
  条件: (K : ι -> 理想 S)
  结论: (⨅ i, (K i).comap f).map f = iInf K
  证明: (giMapComap f hf).l_iInf_u _

Depends on / 依赖: giMapComap, l_iInf_u
-/
theorem map_iInf_comap_of_surjective (K : ι -> Ideal S) : (⨅ i, (K i).comap f).map f = iInf K :=
  (giMapComap f hf).l_iInf_u _

/--
theorem `mem_image_of_mem_map_of_surjective` / 定理 `mem_image_of_mem_map_of_surjective`

English:
theorem mem_image_of_mem_map_of_surjective
  given: {I : Ideal R} {y} (H : y in map f I)
  statement: y in f '' I
  proof: Submodule.span_induction (hx := H) (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩

中文:
定理 mem_image_of_mem_map_of_surjective
  条件: {I : 理想 R} {y} (H : y in map f I)
  结论: y in f '' I
  证明: Submodule.span_induction (hx := H) (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩

Depends on / 依赖: I.add_mem, I.mul_mem_left, I.zero_mem, Submodule, Submodule.span_induction, add_mem, map_add, map_mul, map_zero, mul_mem_left, span_induction, zero_mem
-/
theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y in map f I) : y in f '' I :=
  Submodule.span_induction (hx := H) (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩

/--
theorem `mem_map_iff_of_surjective` / 定理 `mem_map_iff_of_surjective`

English:
theorem mem_map_iff_of_surjective
  given: {I : Ideal R} {y}
  statement: y in map f I ↔ exists x, x in I ∧ f x = y
  proof: ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩

中文:
定理 mem_map_iff_of_surjective
  条件: {I : 理想 R} {y}
  结论: y in map f I ↔ 存在 x, x in I ∧ f x = y
  证明: ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩

Depends on / 依赖: Set.mem_image, hx.left, hx.right, mem_image, mem_image_of_mem_map_of_surjective, mem_map_of_mem
-/
theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y in map f I ↔ exists x, x in I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩

/--
theorem `le_map_of_comap_le_of_surjective` / 定理 `le_map_of_comap_le_of_surjective`

English:
theorem le_map_of_comap_le_of_surjective
  statement: comap f K <= I -> K <= map f I
  proof: fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h

中文:
定理 le_map_of_comap_le_of_surjective
  结论: comap f K <= I -> K <= map f I
  证明: fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h
-/
theorem le_map_of_comap_le_of_surjective : comap f K <= I -> K <= map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h

end

/--
theorem `map_comap_eq_self_of_equiv` / 定理 `map_comap_eq_self_of_equiv`

English:
theorem map_comap_eq_self_of_equiv
  statement: {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
  proof: I.map_comap_of_surjective e (EquivLike.surjective e)

中文:
定理 map_comap_eq_self_of_equiv
  结论: {E : 类型} [等价状 E R S] [环等价类 E R S] (e : E)
  证明: I.map_comap_of_surjective e (EquivLike.surjective e)

Depends on / 依赖: EquivLike, EquivLike.surjective, I.map_comap_of_surjective, map_comap_of_surjective, surjective
-/
theorem map_comap_eq_self_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    (I : Ideal S) : map e (comap e I) = I :=
  I.map_comap_of_surjective e (EquivLike.surjective e)

/--
theorem `map_eq_submodule_map` / 定理 `map_eq_submodule_map`

English:
theorem map_eq_submodule_map
  given: (f : R ->+* S) [h : RingHomSurjective f] (I : Ideal R)
  proof: Submodule.ext fun _ => mem_map_iff_of_surjective f h.1

中文:
定理 map_eq_submodule_map
  条件: (f : R ->+* S) [h : RingHomSurjective f] (I : 理想 R)
  证明: Submodule.ext fun _ => mem_map_iff_of_surjective f h.1

Depends on / 依赖: Submodule, Submodule.ext, mem_map_iff_of_surjective
-/
theorem map_eq_submodule_map (f : R ->+* S) [h : RingHomSurjective f] (I : Ideal R) :
    I.map f = Submodule.map f.toSemilinearMap I :=
  Submodule.ext fun _ => mem_map_iff_of_surjective f h.1

instance (priority := low) (f : R ->+* S) [RingHomSurjective f] (I : Ideal R) [I.IsTwoSided] :
    (I.map f).IsTwoSided where
  mul_mem_of_left b ha := by
    rw [map_eq_submodule_map] at ha ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := f.surjective b
    rw [RingHom.coe_toSemilinearMap]; rw [← map_mul]
    exact ⟨_, I.mul_mem_right _ ha, rfl⟩

open Function in
/--
theorem `IsMaximal.comap_piEvalRingHom` / 定理 `IsMaximal.comap_piEvalRingHom`

English:
theorem IsMaximal.comap_piEvalRingHom
  statement: {ι : Type*} {R : ι -> Type*} [forall i, Semiring (R i)]
  proof: by
  refine isMaximal_iff.mpr ⟨I.ne_top_iff_one.mp h.ne_top, fun J x le hxI hxJ => ?_⟩
  have ⟨r, y, hy, eq⟩ := h.exists_inv hxI
  classical
  convert!
    J.add_mem (J.mul_mem_left (update 0 i r) hxJ) (b := update 1 i y)
      (le <| by apply update_self i y 1 ▸ hy)
  ext j
  obtain rfl | ne := eq_or_ne j i
  · simpa [eq_comm] using eq
  · simp [update_of_ne ne]

中文:
定理 是极大.comap_piEvalRingHom
  结论: {ι : 类型} {R : ι -> 类型} [对任意 i, 半环 (R i)]
  证明: by
  refine isMaximal_iff.mpr ⟨I.ne_top_iff_one.mp h.ne_top, fun J x le hxI hxJ => ?_⟩
  have ⟨r, y, hy, eq⟩ := h.exists_inv hxI
  classical
  convert!
    J.add_mem (J.mul_mem_left (update 0 i r) hxJ) (b := update 1 i y)
      (le <| by apply update_self i y 1 ▸ hy)
  ext j
  obtain rfl | ne := eq_or_ne j i
  · simpa [eq_comm] using eq
  · simp [update_of_ne ne]

Depends on / 依赖: I.ne_top_iff_one.mp, J.add_mem, J.mul_mem_left, add_mem, classical, convert, eq_comm, eq_or_ne, exists_inv, h.exists_inv, h.ne_top, isMaximal_iff, isMaximal_iff.mpr, mul_mem_left, ne_top, ne_top_iff_one, update, update_of_ne, update_self
-/
theorem IsMaximal.comap_piEvalRingHom {ι : Type*} {R : ι -> Type*} [forall i, Semiring (R i)]
    {i : ι} {I : Ideal (R i)} (h : I.IsMaximal) : (I.comap <| Pi.evalRingHom R i).IsMaximal := by
  refine isMaximal_iff.mpr ⟨I.ne_top_iff_one.mp h.ne_top, fun J x le hxI hxJ => ?_⟩
  have ⟨r, y, hy, eq⟩ := h.exists_inv hxI
  classical
  convert!
    J.add_mem (J.mul_mem_left (update 0 i r) hxJ) (b := update 1 i y)
      (le <| by apply update_self i y 1 ▸ hy)
  ext j
  obtain rfl | ne := eq_or_ne j i
  · simpa [eq_comm] using eq
  · simp [update_of_ne ne]

/--
theorem `comap_le_comap_iff_of_surjective` / 定理 `comap_le_comap_iff_of_surjective`

English:
theorem comap_le_comap_iff_of_surjective
  given: (hf : Function.Surjective f) (I J : Ideal S)
  proof: ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

中文:
定理 comap_le_comap_iff_of_surjective
  条件: (hf : 函数.满射 f) (I J : 理想 S)
  证明: ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

Depends on / 依赖: le.trans, le_comap_of_map_le, map_comap_of_surjective, map_le_of_le_comap, symm.le.trans
-/
theorem comap_le_comap_iff_of_surjective (hf : Function.Surjective f) (I J : Ideal S) :
    comap f I <= comap f J ↔ I <= J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

/-- The map on ideals induced by a surjective map preserves inclusion. -/
@[simps]
/--
Definition of `orderEmbeddingOfSurjective` / `orderEmbeddingOfSurjective` 的定义

English:
definition orderEmbeddingOfSurjective
  signature: (hf : Function.Surjective f)
  body: comap f
  inj' _ _ eq := SetLike.ext' (Set.preimage_injective.mpr hf <| SetLike.ext'_iff.mp eq)
  map_rel_iff' := comap_le_comap_iff_of_surjective _ hf ..

中文:
定义 orderEmbeddingOfSurjective
  签名: (hf : 函数.满射 f)
  定义体: comap f
  inj' _ _ eq := SetLike.ext' (Set.preimage_injective.mpr hf <| SetLike.ext'_iff.mp eq)
  map_rel_iff' := comap_le_comap_iff_of_surjective _ hf ..
-/
def orderEmbeddingOfSurjective (hf : Function.Surjective f) : Ideal S ↪o Ideal R where
  toFun := comap f
  inj' _ _ eq := SetLike.ext' (Set.preimage_injective.mpr hf <| SetLike.ext'_iff.mp eq)
  map_rel_iff' := comap_le_comap_iff_of_surjective _ hf ..

/--
theorem `map_eq_top_or_isMaximal_of_surjective` / 定理 `map_eq_top_or_isMaximal_of_surjective`

English:
theorem map_eq_top_or_isMaximal_of_surjective
  statement: (hf : Function.Surjective f) {I : Ideal R}
  proof: or_iff_not_imp_left.2 fun ne_top => ⟨⟨ne_top, fun _J hJ => comap_injective_of_surjective f hf
    H.1.2 _ (le_comap_map.trans_lt <| (orderEmbeddingOfSurjective f hf).strictMono hJ)⟩⟩

中文:
定理 map_eq_top_or_isMaximal_of_surjective
  结论: (hf : 函数.满射 f) {I : 理想 R}
  证明: or_iff_not_imp_left.2 fun ne_top => ⟨⟨ne_top, fun _J hJ => comap_injective_of_surjective f hf
    H.1.2 _ (le_comap_map.trans_lt <| (orderEmbeddingOfSurjective f hf).strictMono hJ)⟩⟩

Depends on / 依赖: comap_injective_of_surjective, le_comap_map, le_comap_map.trans_lt, ne_top, or_iff_not_imp_left, orderEmbeddingOfSurjective, strictMono, trans_lt
-/
theorem map_eq_top_or_isMaximal_of_surjective (hf : Function.Surjective f) {I : Ideal R}
    (H : IsMaximal I) : map f I = ⊤ ∨ IsMaximal (map f I) :=
or_iff_not_imp_left.2 fun ne_top => ⟨⟨ne_top, fun _J hJ => comap_injective_of_surjective f hf
    H.1.2 _ (le_comap_map.trans_lt <| (orderEmbeddingOfSurjective f hf).strictMono hJ)⟩⟩

end Surjective

section Pi

variable {ι : Type*} {R : ι -> Type*} [forall i, Semiring (R i)]

/--
theorem `map_evalRingHom_pi` / 定理 `map_evalRingHom_pi`

English:
theorem map_evalRingHom_pi
  given: {I : Π i, Ideal (R i)} (i : ι)
  proof: by
  ext r
  rw [mem_map_iff_of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)]
  classical refine ⟨?_, fun hr => ⟨_, single_mem_pi hr, by simp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact hr i

#adaptation_note

中文:
定理 map_evalRingHom_pi
  条件: {I : Π i, 理想 (R i)} (i : ι)
  证明: by
  ext r
  rw [mem_map_iff_of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)]
  classical refine ⟨?_, fun hr => ⟨_, single_mem_pi hr, by simp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact hr i

#adaptation_note

Depends on / 依赖: Function, Function.surjective_eval, Pi.evalRingHom, classical, evalRingHom, mem_map_iff_of_surjective, single_mem_pi, surjective_eval
-/
theorem map_evalRingHom_pi {I : Π i, Ideal (R i)} (i : ι) :
    (pi I).map (Pi.evalRingHom R i) = I i := by
  ext r
  rw [mem_map_iff_of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)]
  classical refine ⟨?_, fun hr => ⟨_, single_mem_pi hr, by simp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact hr i

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `piOrderIso` / `piOrderIso` 的定义

English:
definition piOrderIso
  signature: [Finite ι]
  body: .symm
  { toFun := pi
    invFun I i := I.map (Pi.evalRingHom R i)
    left_inv _ := funext map_evalRingHom_pi
    right_inv I := by
      ext r
      simp_rw [mem_pi, mem_map_iff_of_surjective (Pi.evalRingHom R _) (Function.surjective_eval _)]
      refine ⟨(fun ⟨r', hr'⟩ => ?_) ∘ Classical.skolem.mp, fun hr i => ⟨r, hr, rfl⟩⟩
      have := Fintype.ofFinite ι
      classical rw [show r = ∑ i, Pi.single i 1 * r' i from funext fun i => by
        rw [← (hr' _).2]; rw [Finset.sum_apply]; rw [Fintype.sum_eq_single i fun j ne => by simp [ne]]; simp]
      exact sum_mem fun i _ => I.mul_mem_left _ (hr' i).1
    map_rel_iff' := pi_le_pi_iff }

中文:
定义 piOrderIso
  签名: [有限 ι]
  定义体: .symm
  { toFun := pi
    invFun I i := I.map (Pi.evalRingHom R i)
    left_inv _ := funext map_evalRingHom_pi
    right_inv I := by
      ext r
      simp_rw [mem_pi, mem_map_iff_of_surjective (Pi.evalRingHom R _) (Function.surjective_eval _)]
      refine ⟨(fun ⟨r', hr'⟩ => ?_) ∘ Classical.skolem.mp, fun hr i => ⟨r, hr, rfl⟩⟩
      have := Fintype.ofFinite ι
      classical rw [show r = ∑ i, Pi.single i 1 * r' i from funext fun i => by
        rw [← (hr' _).2]; rw [Finset.sum_apply]; rw [Fintype.sum_eq_single i fun j ne => by simp [ne]]; simp]
      exact sum_mem fun i _ => I.mul_mem_left _ (hr' i).1
    map_rel_iff' := pi_le_pi_iff }
-/
@[simps!] def piOrderIso [Finite ι] : Ideal (Π i, R i) ≃o Π i, Ideal (R i) := .symm
  { toFun := pi
    invFun I i := I.map (Pi.evalRingHom R i)
    left_inv _ := funext map_evalRingHom_pi
    right_inv I := by
      ext r
      simp_rw [mem_pi, mem_map_iff_of_surjective (Pi.evalRingHom R _) (Function.surjective_eval _)]
      refine ⟨(fun ⟨r', hr'⟩ => ?_) ∘ Classical.skolem.mp, fun hr i => ⟨r, hr, rfl⟩⟩
      have := Fintype.ofFinite ι
      classical rw [show r = ∑ i, Pi.single i 1 * r' i from funext fun i => by
        rw [← (hr' _).2]; rw [Finset.sum_apply]; rw [Fintype.sum_eq_single i fun j ne => by simp [ne]]; simp]
      exact sum_mem fun i _ => I.mul_mem_left _ (hr' i).1
    map_rel_iff' := pi_le_pi_iff }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] [forall i, IsPrincipalIdealRing (R i)] : IsPrincipalIdealRing (Π i, R i) where
  body: by
    rw [← piOrderIso.symm_apply_apply I]
    exact ⟨_, congr(pi $(funext fun i =>
      (Submodule.IsPrincipal.span_singleton_generator _).symm)).trans pi_span⟩

中文:
实例 [有限
  签名: ι] [对任意 i, 是主理想环 (R i)] : 是主理想环 (Π i, R i) where
  定义体: by
    rw [← piOrderIso.symm_apply_apply I]
    exact ⟨_, congr(pi $(funext fun i =>
      (Submodule.IsPrincipal.span_singleton_generator _).symm)).trans pi_span⟩

Depends on / 依赖: IsPrincipal, Submodule, Submodule.IsPrincipal.span_singleton_generator, piOrderIso, piOrderIso.symm_apply_apply, pi_span, span_singleton_generator, symm_apply_apply
-/
instance [Finite ι] [forall i, IsPrincipalIdealRing (R i)] : IsPrincipalIdealRing (Π i, R i) where
  principal I := by
    rw [← piOrderIso.symm_apply_apply I]
    exact ⟨_, congr(pi $(funext fun i =>
      (Submodule.IsPrincipal.span_singleton_generator _).symm)).trans pi_span⟩

end Pi

section Injective

/--
theorem `comap_bot_le_of_injective` / 定理 `comap_bot_le_of_injective`

English:
theorem comap_bot_le_of_injective
  given: (hf : Function.Injective f)
  statement: comap f ⊥ <= I
  proof: by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap]; rw [Submodule.mem_bot]; rw [← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥

中文:
定理 comap_bot_le_of_injective
  条件: (hf : 函数.单射 f)
  结论: comap f ⊥ <= I
  证明: by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap]; rw [Submodule.mem_bot]; rw [← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥

Depends on / 依赖: Eq.symm, Submodule, Submodule.mem_bot, Submodule.zero_mem, bot_le, le_trans, map_zero, mem_bot, mem_comap, zero_mem
-/
theorem comap_bot_le_of_injective (hf : Function.Injective f) : comap f ⊥ <= I := by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap]; rw [Submodule.mem_bot]; rw [← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥

/--
theorem `comap_bot_of_injective` / 定理 `comap_bot_of_injective`

English:
theorem comap_bot_of_injective
  given: (hf : Function.Injective f)
  statement: Ideal.comap f ⊥ = ⊥
  proof: le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)

中文:
定理 comap_bot_of_injective
  条件: (hf : 函数.单射 f)
  结论: 理想.comap f ⊥ = ⊥
  证明: le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)

Depends on / 依赖: Ideal.comap_bot_le_of_injective, comap_bot_le_of_injective, le_bot_iff, le_bot_iff.mp
-/
theorem comap_bot_of_injective (hf : Function.Injective f) : Ideal.comap f ⊥ = ⊥ :=
  le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)

end Injective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map f I) = I`. -/
@[simp]
/--
theorem `map_of_equiv` / 定理 `map_of_equiv`

English:
theorem map_of_equiv
  given: {I : Ideal R} (f : R ≃+* S)
  proof: by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [map_map]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [map_id]

中文:
定理 map_of_equiv
  条件: {I : 理想 R} (f : R ≃+* S)
  证明: by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [map_map]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [map_id]

Depends on / 依赖: RingEquiv, RingEquiv.symm_comp, RingEquiv.toRingHom_eq_coe, map_id, map_map, symm_comp, toRingHom_eq_coe
-/
theorem map_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.map (f : R ->+* S)).map (f.symm : S ->+* R) = I := by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [map_map]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [map_id]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`. -/
@[simp]
/--
theorem `comap_of_equiv` / 定理 `comap_of_equiv`

English:
theorem comap_of_equiv
  given: {I : Ideal R} (f : R ≃+* S)
  proof: by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [comap_comap]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [comap_id]

中文:
定理 comap_of_equiv
  条件: {I : 理想 R} (f : R ≃+* S)
  证明: by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [comap_comap]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [comap_id]

Depends on / 依赖: RingEquiv, RingEquiv.symm_comp, RingEquiv.toRingHom_eq_coe, comap_comap, comap_id, symm_comp, toRingHom_eq_coe
-/
theorem comap_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.comap (f.symm : S ->+* R)).comap (f : R ->+* S) = I := by
  rw [← RingEquiv.toRingHom_eq_coe]; rw [← RingEquiv.toRingHom_eq_coe]; rw [comap_comap]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]; rw [comap_id]

/--
theorem `map_comap_of_equiv` / 定理 `map_comap_of_equiv`

English:
theorem map_comap_of_equiv
  given: {I : Ideal R} (f : R ≃+* S)
  statement: I.map (f : R ->+* S) = I.comap f.symm
  proof: le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
    (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))

中文:
定理 map_comap_of_equiv
  条件: {I : 理想 R} (f : R ≃+* S)
  结论: I.map (f : R ->+* S) = I.comap f.symm
  证明: le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
    (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))

Depends on / 依赖: Equiv.left_inv, Equiv.right_inv, Ideal.comap_le_map_of_inverse, Ideal.map_le_comap_of_inverse, comap_le_map_of_inverse, le_antisymm, left_inv, map_le_comap_of_inverse, right_inv
-/
theorem map_comap_of_equiv {I : Ideal R} (f : R ≃+* S) : I.map (f : R ->+* S) = I.comap f.symm :=
  le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
    (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I = map f I`. -/
@[simp]
/--
theorem `comap_symm` / 定理 `comap_symm`

English:
theorem comap_symm
  given: {I : Ideal R} (f : R ≃+* S)
  statement: I.comap f.symm = I.map f
  proof: (map_comap_of_equiv f).symm

中文:
定理 comap_symm
  条件: {I : 理想 R} (f : R ≃+* S)
  结论: I.comap f.symm = I.map f
  证明: (map_comap_of_equiv f).symm

Depends on / 依赖: map_comap_of_equiv
-/
theorem comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.symm = I.map f :=
  (map_comap_of_equiv f).symm

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = comap f I`. -/
@[simp]
/--
theorem `map_symm` / 定理 `map_symm`

English:
theorem map_symm
  given: {I : Ideal S} (f : R ≃+* S)
  statement: I.map f.symm = I.comap f
  proof: map_comap_of_equiv (RingEquiv.symm f)

@[simp]

中文:
定理 map_symm
  条件: {I : 理想 S} (f : R ≃+* S)
  结论: I.map f.symm = I.comap f
  证明: map_comap_of_equiv (RingEquiv.symm f)

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.symm, map_comap_of_equiv
-/
theorem map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.comap f :=
  map_comap_of_equiv (RingEquiv.symm f)

@[simp]
/--
theorem `symm_apply_mem_of_equiv_iff` / 定理 `symm_apply_mem_of_equiv_iff`

English:
theorem symm_apply_mem_of_equiv_iff
  given: {I : Ideal R} {f : R ≃+* S} {y : S}
  proof: by
  rw [← comap_symm]; rw [mem_comap]

@[simp]

中文:
定理 symm_apply_mem_of_equiv_iff
  条件: {I : 理想 R} {f : R ≃+* S} {y : S}
  证明: by
  rw [← comap_symm]; rw [mem_comap]

@[simp]

Depends on / 依赖: comap_symm, mem_comap
-/
theorem symm_apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {y : S} :
    f.symm y in I ↔ y in I.map f := by
  rw [← comap_symm]; rw [mem_comap]

@[simp]
/--
theorem `apply_mem_of_equiv_iff` / 定理 `apply_mem_of_equiv_iff`

English:
theorem apply_mem_of_equiv_iff
  given: {I : Ideal R} {f : R ≃+* S} {x : R}
  proof: by
  rw [← comap_symm]; rw [Ideal.mem_comap]; rw [f.symm_apply_apply]

中文:
定理 apply_mem_of_equiv_iff
  条件: {I : 理想 R} {f : R ≃+* S} {x : R}
  证明: by
  rw [← comap_symm]; rw [Ideal.mem_comap]; rw [f.symm_apply_apply]

Depends on / 依赖: Ideal.mem_comap, comap_symm, f.symm_apply_apply, mem_comap, symm_apply_apply
-/
theorem apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {x : R} :
    f x in I.map f ↔ x in I := by
  rw [← comap_symm]; rw [Ideal.mem_comap]; rw [f.symm_apply_apply]

/--
theorem `mem_map_of_equiv` / 定理 `mem_map_of_equiv`

English:
theorem mem_map_of_equiv
  statement: {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
  proof: by
  constructor
  · intro h
    simp_rw [show map e I = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : R ≃+* S)] at h
    exact ⟨(EquivLike.toEquiv e).symm y, h, (EquivLike.toEquiv e).apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem e hx

中文:
定理 mem_map_of_equiv
  结论: {E : 类型} [等价状 E R S] [环等价类 E R S] (e : E)
  证明: by
  constructor
  · intro h
    simp_rw [show map e I = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : R ≃+* S)] at h
    exact ⟨(EquivLike.toEquiv e).symm y, h, (EquivLike.toEquiv e).apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem e hx

Depends on / 依赖: EquivLike, EquivLike.toEquiv, RingEquivClass, RingEquivClass.toRingEquiv, apply_symm_apply, map_comap_of_equiv, mem_map_of_mem, simp_rw, toEquiv, toRingEquiv
-/
theorem mem_map_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {I : Ideal R} (y : S) : y in map e I ↔ exists x in I, e x = y := by
  constructor
  · intro h
    simp_rw [show map e I = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : R ≃+* S)] at h
    exact ⟨(EquivLike.toEquiv e).symm y, h, (EquivLike.toEquiv e).apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem e hx

/--
lemma `map_primeCompl_comap_of_surjective` / 引理 `map_primeCompl_comap_of_surjective`

English:
lemma map_primeCompl_comap_of_surjective
  given: (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime]
  proof: by
  rw [SetLike.ext_iff]; rw [hf.forall]
  grind [Submonoid.mem_map, mem_primeCompl_iff, mem_comap]

中文:
引理 map_primeCompl_comap_of_surjective
  条件: (hf : 函数.满射 f) (p : 理想 S) [p.是素]
  证明: by
  rw [SetLike.ext_iff]; rw [hf.forall]
  grind [Submonoid.mem_map, mem_primeCompl_iff, mem_comap]

Depends on / 依赖: SetLike, SetLike.ext_iff, Submonoid, Submonoid.mem_map, ext_iff, hf.forall, mem_comap, mem_map, mem_primeCompl_iff
-/
lemma map_primeCompl_comap_of_surjective (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    Submonoid.map f (p.comap f).primeCompl = p.primeCompl := by
  rw [SetLike.ext_iff]; rw [hf.forall]
  grind [Submonoid.mem_map, mem_primeCompl_iff, mem_comap]

/--
lemma `_root_.RingEquiv.map_primeCompl_comap_eq` / 引理 `_root_.RingEquiv.map_primeCompl_comap_eq`

English:
lemma _root_.RingEquiv.map_primeCompl_comap_eq
  given: (e : R ≃+* S) (p : Ideal S) [p.IsPrime]
  proof: p.map_primeCompl_comap_of_surjective e e.surjective

中文:
引理 _root_.环等价.map_primeCompl_comap_eq
  条件: (e : R ≃+* S) (p : 理想 S) [p.是素]
  证明: p.map_primeCompl_comap_of_surjective e e.surjective

Depends on / 依赖: e.surjective, map_primeCompl_comap_of_surjective, p.map_primeCompl_comap_of_surjective, surjective
-/
lemma _root_.RingEquiv.map_primeCompl_comap_eq (e : R ≃+* S) (p : Ideal S) [p.IsPrime] :
    (p.comap e).primeCompl.map e = p.primeCompl :=
  p.map_primeCompl_comap_of_surjective e e.surjective

section Bijective

variable (hf : Function.Bijective f) {I : Ideal R} {K : Ideal S}
include hf

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `relIsoOfBijective` / `relIsoOfBijective` 的定义

English:
definition relIsoOfBijective
  signature: : Ideal S ≃o Ideal R where
  body: comap f
  invFun := map f
  left_inv := map_comap_of_surjective _ hf.2
  right_inv J :=
    le_antisymm
      (fun _ h => have ⟨y, hy, eq⟩ := (mem_map_iff_of_surjective _ hf.2).mp h; hf.1 eq ▸ hy)
      le_comap_map
  map_rel_iff' {_ _} := by
    refine ⟨fun h => ?_, comap_mono⟩
    have := map_mono (f := f) h
    simpa only [Equiv.coe_fn_mk, map_comap_of_surjective f hf.2] using this

中文:
定义 relIsoOfBijective
  签名: : 理想 S ≃o 理想 R where
  定义体: comap f
  invFun := map f
  left_inv := map_comap_of_surjective _ hf.2
  right_inv J :=
    le_antisymm
      (fun _ h => have ⟨y, hy, eq⟩ := (mem_map_iff_of_surjective _ hf.2).mp h; hf.1 eq ▸ hy)
      le_comap_map
  map_rel_iff' {_ _} := by
    refine ⟨fun h => ?_, comap_mono⟩
    have := map_mono (f := f) h
    simpa only [Equiv.coe_fn_mk, map_comap_of_surjective f hf.2] using this
-/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := map_comap_of_surjective _ hf.2
  right_inv J :=
    le_antisymm
      (fun _ h => have ⟨y, hy, eq⟩ := (mem_map_iff_of_surjective _ hf.2).mp h; hf.1 eq ▸ hy)
      le_comap_map
  map_rel_iff' {_ _} := by
    refine ⟨fun h => ?_, comap_mono⟩
    have := map_mono (f := f) h
    simpa only [Equiv.coe_fn_mk, map_comap_of_surjective f hf.2] using this

/--
theorem `comap_le_iff_le_map` / 定理 `comap_le_iff_le_map`

English:
theorem comap_le_iff_le_map
  statement: comap f K <= I ↔ K <= map f I
  proof: ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩

中文:
定理 comap_le_iff_le_map
  结论: comap f K <= I ↔ K <= map f I
  证明: ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩

Depends on / 依赖: comap_mono, hf.right, le_map_of_comap_le_of_surjective, relIsoOfBijective, right_inv
-/
theorem comap_le_iff_le_map : comap f K <= I ↔ K <= map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩

/--
theorem `map_eq_top_of_bijective` / 定理 `map_eq_top_of_bijective`

English:
theorem map_eq_top_of_bijective
  statement: I.map f = ⊤ ↔ I = ⊤
  proof: by
  rw [eq_top_iff]; rw [← comap_le_iff_le_map f hf]; rw [comap_top]; rw [top_le_iff]

中文:
定理 map_eq_top_of_bijective
  结论: I.map f = ⊤ ↔ I = ⊤
  证明: by
  rw [eq_top_iff]; rw [← comap_le_iff_le_map f hf]; rw [comap_top]; rw [top_le_iff]

Depends on / 依赖: comap_le_iff_le_map, comap_top, eq_top_iff, top_le_iff
-/
theorem map_eq_top_of_bijective : I.map f = ⊤ ↔ I = ⊤ := by
  rw [eq_top_iff]; rw [← comap_le_iff_le_map f hf]; rw [comap_top]; rw [top_le_iff]

/--
theorem `comap_map_of_bijective` / 定理 `comap_map_of_bijective`

English:
theorem comap_map_of_bijective
  statement: (I.map f).comap f = I
  proof: le_antisymm ((comap_le_iff_le_map f hf).mpr fun _ => id) le_comap_map

中文:
定理 comap_map_of_bijective
  结论: (I.map f).comap f = I
  证明: le_antisymm ((comap_le_iff_le_map f hf).mpr fun _ => id) le_comap_map

Depends on / 依赖: comap_le_iff_le_map, le_antisymm, le_comap_map
-/
theorem comap_map_of_bijective : (I.map f).comap f = I :=
  le_antisymm ((comap_le_iff_le_map f hf).mpr fun _ => id) le_comap_map

/--
theorem `isMaximal_map_iff_of_bijective` / 定理 `isMaximal_map_iff_of_bijective`

English:
theorem isMaximal_map_iff_of_bijective
  statement: IsMaximal (map f I) ↔ IsMaximal I
  proof: by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).symm.isCoatom_iff _

中文:
定理 isMaximal_map_iff_of_bijective
  结论: 是极大 (map f I) ↔ 是极大 I
  证明: by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).symm.isCoatom_iff _

Depends on / 依赖: isCoatom_iff, isMaximal_def, relIsoOfBijective, symm.isCoatom_iff
-/
theorem isMaximal_map_iff_of_bijective : IsMaximal (map f I) ↔ IsMaximal I := by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).symm.isCoatom_iff _

/--
theorem `isMaximal_comap_iff_of_bijective` / 定理 `isMaximal_comap_iff_of_bijective`

English:
theorem isMaximal_comap_iff_of_bijective
  statement: IsMaximal (comap f K) ↔ IsMaximal K
  proof: by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).isCoatom_iff _

alias ⟨_, IsMaximal.map_bijective⟩ := isMaximal_map_iff_of_bijective
alias ⟨_, IsMaximal.comap_bijective⟩ := isMaximal_comap_iff_of_bijective

中文:
定理 isMaximal_comap_iff_of_bijective
  结论: 是极大 (comap f K) ↔ 是极大 K
  证明: by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).isCoatom_iff _

alias ⟨_, IsMaximal.map_bijective⟩ := isMaximal_map_iff_of_bijective
alias ⟨_, IsMaximal.comap_bijective⟩ := isMaximal_comap_iff_of_bijective

Depends on / 依赖: isCoatom_iff, isMaximal_def, relIsoOfBijective
-/
theorem isMaximal_comap_iff_of_bijective : IsMaximal (comap f K) ↔ IsMaximal K := by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).isCoatom_iff _

alias ⟨_, IsMaximal.map_bijective⟩ := isMaximal_map_iff_of_bijective
alias ⟨_, IsMaximal.comap_bijective⟩ := isMaximal_comap_iff_of_bijective

/--
Instance `map_isMaximal_of_equiv` / 实例 `map_isMaximal_of_equiv`

English:
instance map_isMaximal_of_equiv
  signature: {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
  body: hp.map_bijective e (EquivLike.bijective e)

中文:
实例 map_isMaximal_of_equiv
  签名: {E : 类型} [等价状 E R S] [环等价类 E R S] (e : E)
  定义体: hp.map_bijective e (EquivLike.bijective e)

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, hp.map_bijective, map_bijective
-/
instance map_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal R} [hp : p.IsMaximal] : (map e p).IsMaximal :=
  hp.map_bijective e (EquivLike.bijective e)

/--
Instance `comap_isMaximal_of_equiv` / 实例 `comap_isMaximal_of_equiv`

English:
instance comap_isMaximal_of_equiv
  signature: {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
  body: hp.comap_bijective e (EquivLike.bijective e)

中文:
实例 comap_isMaximal_of_equiv
  签名: {E : 类型} [等价状 E R S] [环等价类 E R S] (e : E)
  定义体: hp.comap_bijective e (EquivLike.bijective e)

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, comap_bijective, hp.comap_bijective
-/
instance comap_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal S} [hp : p.IsMaximal] : (comap e p).IsMaximal :=
  hp.comap_bijective e (EquivLike.bijective e)

/--
theorem `isMaximal_iff_of_bijective` / 定理 `isMaximal_iff_of_bijective`

English:
theorem isMaximal_iff_of_bijective
  statement: (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal
  proof: ⟨fun h => map_bot (f := f) ▸ h.map_bijective f hf, fun h => have e := RingEquiv.ofBijective f hf
    map_bot (f := e.symm) ▸ h.map_bijective _ e.symm.bijective⟩

中文:
定理 isMaximal_iff_of_bijective
  结论: (⊥ : 理想 R).是极大 ↔ (⊥ : 理想 S).是极大
  证明: ⟨fun h => map_bot (f := f) ▸ h.map_bijective f hf, fun h => have e := RingEquiv.ofBijective f hf
    map_bot (f := e.symm) ▸ h.map_bijective _ e.symm.bijective⟩

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective, e.symm, e.symm.bijective, h.map_bijective, map_bijective, map_bot, ofBijective
-/
theorem isMaximal_iff_of_bijective : (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h => map_bot (f := f) ▸ h.map_bijective f hf, fun h => have e := RingEquiv.ofBijective f hf
    map_bot (f := e.symm) ▸ h.map_bijective _ e.symm.bijective⟩

end Bijective

end Semiring

section Ring

variable {F : Type*} [Ring R] [Ring S]
variable [FunLike F R S] [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

/--
theorem `comap_map_of_surjective` / 定理 `comap_map_of_surjective`

English:
theorem comap_map_of_surjective
  given: (hf : Function.Surjective f) (I : Ideal R)
  proof: le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
⟨s, hsi, r - s, (Submodule.mem_bot S).2 by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))

中文:
定理 comap_map_of_surjective
  条件: (hf : 函数.满射 f) (I : 理想 R)
  证明: le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
⟨s, hsi, r - s, (Submodule.mem_bot S).2 by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))

Depends on / 依赖: Submodule, Submodule.mem_bot, Submodule.mem_sup, add_sub_cancel, bot_le, comap_mono, le_antisymm, le_rfl, map_le_iff_le_comap, map_sub, mem_bot, mem_image_of_mem_map_of_surjective, mem_sup, sub_self, sup_le
-/
theorem comap_map_of_surjective (hf : Function.Surjective f) (I : Ideal R) :
    comap f (map f I) = I ⊔ comap f ⊥ :=
  le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
⟨s, hsi, r - s, (Submodule.mem_bot S).2 by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))

/--
theorem `coheight_comap_of_surjective` / 定理 `coheight_comap_of_surjective`

English:
theorem coheight_comap_of_surjective
  given: (hf : Function.Surjective f) (I : Ideal S)
  proof: by
  let φ := orderEmbeddingOfSurjective f hf
  refine (Order.coheight_eq_of_strictMono φ φ.strictMono (fun J K h => ⟨K.map f, ?_, ?_⟩) I).symm
  · rw [← J.map_comap_of_surjective f hf]
    apply lt_of_le_not_ge (map_mono h.le)
    simpa [map_le_iff_le_comap, φ] using h.not_ge
  · exact (K.comap_map_of_surjective f hf).trans (sup_of_le_left ((comap_mono bot_le).trans h.le))

中文:
定理 coheight_comap_of_surjective
  条件: (hf : 函数.满射 f) (I : 理想 S)
  证明: by
  let φ := orderEmbeddingOfSurjective f hf
  refine (Order.coheight_eq_of_strictMono φ φ.strictMono (fun J K h => ⟨K.map f, ?_, ?_⟩) I).symm
  · rw [← J.map_comap_of_surjective f hf]
    apply lt_of_le_not_ge (map_mono h.le)
    simpa [map_le_iff_le_comap, φ] using h.not_ge
  · exact (K.comap_map_of_surjective f hf).trans (sup_of_le_left ((comap_mono bot_le).trans h.le))

Depends on / 依赖: J.map_comap_of_surjective, K.comap_map_of_surjective, K.map, Order.coheight_eq_of_strictMono, bot_le, coheight_eq_of_strictMono, comap_map_of_surjective, comap_mono, h.le, h.not_ge, lt_of_le_not_ge, map_comap_of_surjective, map_le_iff_le_comap, map_mono, not_ge, orderEmbeddingOfSurjective, strictMono, sup_of_le_left
-/
theorem coheight_comap_of_surjective (hf : Function.Surjective f) (I : Ideal S) :
    Order.coheight (I.comap f) = Order.coheight I := by
  let φ := orderEmbeddingOfSurjective f hf
  refine (Order.coheight_eq_of_strictMono φ φ.strictMono (fun J K h => ⟨K.map f, ?_, ?_⟩) I).symm
  · rw [← J.map_comap_of_surjective f hf]
    apply lt_of_le_not_ge (map_mono h.le)
    simpa [map_le_iff_le_comap, φ] using h.not_ge
  · exact (K.comap_map_of_surjective f hf).trans (sup_of_le_left ((comap_mono bot_le).trans h.le))

/--
Definition of `relIsoOfSurjective` / `relIsoOfSurjective` 的定义

English:
definition relIsoOfSurjective
  signature: (hf : Function.Surjective f)
  body: ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
Subtype.ext
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩

中文:
定义 relIsoOfSurjective
  签名: (hf : 函数.满射 f)
  定义体: ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
Subtype.ext
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩

Depends on / 依赖: bot_le, comap_mono
-/
def relIsoOfSurjective (hf : Function.Surjective f) :
    Ideal S ≃o { p : Ideal R // comap f ⊥ <= p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
Subtype.ext
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩

-- May not hold if `R` is a semiring: consider `ℕ →+* ZMod 2`.
/--
theorem `comap_isMaximal_of_surjective` / 定理 `comap_isMaximal_of_surjective`

English:
theorem comap_isMaximal_of_surjective
  given: (hf : Function.Surjective f) {K : Ideal S} [H : IsMaximal K]
  proof: by
  refine ⟨⟨comap_ne_top _ H.1.1, fun J hJ => ?_⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top]; rw [comap_map_of_surjective _ hf]; rw [eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) ?_))
  rw [comap_map_of_surjective _ hf]; rw [sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)

中文:
定理 comap_isMaximal_of_surjective
  条件: (hf : 函数.满射 f) {K : 理想 S} [H : 是极大 K]
  证明: by
  refine ⟨⟨comap_ne_top _ H.1.1, fun J hJ => ?_⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top]; rw [comap_map_of_surjective _ hf]; rw [eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) ?_))
  rw [comap_map_of_surjective _ hf]; rw [sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)

Depends on / 依赖: _root_, _root_.trans, bot_le, comap_map_of_surjective, comap_mono, comap_ne_top, comap_top, congr_arg, eq_top_iff, le_map_of_comap_le_of_surjective, le_of_eq, le_of_lt, le_trans, lt_of_le_of_ne, ne_of_lt, sup_eq_left, sup_le
-/
theorem comap_isMaximal_of_surjective (hf : Function.Surjective f) {K : Ideal S} [H : IsMaximal K] :
    IsMaximal (comap f K) := by
  refine ⟨⟨comap_ne_top _ H.1.1, fun J hJ => ?_⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top]; rw [comap_map_of_surjective _ hf]; rw [eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) ?_))
  rw [comap_map_of_surjective _ hf]; rw [sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)

end Surjective


end Ring

section CommRing

variable {F : Type*} [CommSemiring R] [CommSemiring S]
variable [FunLike F R S] [rc : RingHomClass F R S]
variable (f : F)
variable (I J : Ideal R) (K L : Ideal S)

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: {R} [Semiring R] [FunLike F R S] [RingHomClass F R S]
  proof: le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) in map f I * map f J by
          rw [map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <| by
      rintro _ ⟨_, ⟨r, hri, rfl⟩, _, ⟨s, hsj, rfl⟩, rfl⟩
      simp_rw [← map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))

中文:
定理 map_mul
  结论: {R} [半环 R] [函数状 F R S] [环态射类 F R S]
  证明: le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) in map f I * map f J by
          rw [map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <| by
      rintro _ ⟨_, ⟨r, hri, rfl⟩, _, ⟨s, hsj, rfl⟩, rfl⟩
      simp_rw [← map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))
-/
protected theorem map_mul {R} [Semiring R] [FunLike F R S] [RingHomClass F R S]
    (f : F) (I J : Ideal R) :
    map f (I * J) = map f I * map f J :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) in map f I * map f J by
          rw [map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <| by
      rintro _ ⟨_, ⟨r, hri, rfl⟩, _, ⟨s, hsj, rfl⟩, rfl⟩
      simp_rw [← map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))

/-- The pushforward `Ideal.map` as a (semi)ring homomorphism. -/
@[simps]
/--
Definition of `mapHom` / `mapHom` 的定义

English:
definition mapHom
  signature: : Ideal R ->+* Ideal S where
  body: map f
  map_mul' := Ideal.map_mul f
  map_one' := by simp only [one_eq_top, Ideal.map_top f]
  map_add' I J := Ideal.map_sup f I J
  map_zero' := Ideal.map_bot

中文:
定义 mapHom
  签名: : 理想 R ->+* 理想 S where
  定义体: map f
  map_mul' := Ideal.map_mul f
  map_one' := by simp only [one_eq_top, Ideal.map_top f]
  map_add' I J := Ideal.map_sup f I J
  map_zero' := Ideal.map_bot
-/
def mapHom : Ideal R ->+* Ideal S where
  toFun := map f
  map_mul' := Ideal.map_mul f
  map_one' := by simp only [one_eq_top, Ideal.map_top f]
  map_add' I J := Ideal.map_sup f I J
  map_zero' := Ideal.map_bot

/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (n : Nat)
  statement: map f (I ^ n) = map f I ^ n
  proof: map_pow (mapHom f) I n

中文:
定理 map_pow
  条件: (n : 自然数)
  结论: map f (I ^ n) = map f I ^ n
  证明: map_pow (mapHom f) I n
-/
protected theorem map_pow (n : Nat) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_radical` / 定理 `comap_radical`

English:
theorem comap_radical
  statement: comap f (radical K) = radical (comap f K)
  proof: by
  ext
  simp [radical]

中文:
定理 comap_radical
  结论: comap f (radical K) = radical (comap f K)
  证明: by
  ext
  simp [radical]

Depends on / 依赖: radical
-/
theorem comap_radical : comap f (radical K) = radical (comap f K) := by
  ext
  simp [radical]

variable {K}

/--
theorem `IsRadical.comap` / 定理 `IsRadical.comap`

English:
theorem IsRadical.comap
  given: (hK : K.IsRadical)
  statement: (comap f K).IsRadical
  proof: by
  rw [← hK.radical]; rw [comap_radical]
  apply radical_isRadical

中文:
定理 IsRadical.comap
  条件: (hK : K.IsRadical)
  结论: (comap f K).IsRadical
  证明: by
  rw [← hK.radical]; rw [comap_radical]
  apply radical_isRadical

Depends on / 依赖: comap_radical, hK.radical, radical, radical_isRadical
-/
theorem IsRadical.comap (hK : K.IsRadical) : (comap f K).IsRadical := by
  rw [← hK.radical]; rw [comap_radical]
  apply radical_isRadical

variable {I J L}

/--
theorem `map_radical_le` / 定理 `map_radical_le`

English:
theorem map_radical_le
  statement: map f (radical I) <= radical (map f I)
  proof: map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩

中文:
定理 map_radical_le
  结论: map f (radical I) <= radical (map f I)
  证明: map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩

Depends on / 依赖: map_le_iff_le_comap, map_pow, mem_map_of_mem
-/
theorem map_radical_le : map f (radical I) <= radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩

/--
theorem `le_comap_mul` / 定理 `le_comap_mul`

English:
theorem le_comap_mul
  statement: comap f K * comap f L <= comap f (K * L)
  proof: map_le_iff_le_comap.1
    (Ideal.map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)

中文:
定理 le_comap_mul
  结论: comap f K * comap f L <= comap f (K * L)
  证明: map_le_iff_le_comap.1
    (Ideal.map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)

Depends on / 依赖: Ideal.map_mul, le_rfl, map_le_iff_le_comap, map_mul, mul_mono
-/
theorem le_comap_mul : comap f K * comap f L <= comap f (K * L) :=
map_le_iff_le_comap.1
    (Ideal.map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)

/--
theorem `le_comap_pow` / 定理 `le_comap_pow`

English:
theorem le_comap_pow
  given: (n : Nat)
  statement: K.comap f ^ n <= (K ^ n).comap f
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [Ideal.one_eq_top]; rw [Ideal.one_eq_top]
    exact rfl.le
  | succ n n_ih =>
    rw [pow_succ]; rw [pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)

中文:
定理 le_comap_pow
  条件: (n : 自然数)
  结论: K.comap f ^ n <= (K ^ n).comap f
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [Ideal.one_eq_top]; rw [Ideal.one_eq_top]
    exact rfl.le
  | succ n n_ih =>
    rw [pow_succ]; rw [pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)

Depends on / 依赖: Ideal.le_comap_mul, Ideal.mul_mono_left, Ideal.one_eq_top, le_comap_mul, mul_mono_left, n_ih, one_eq_top, pow_succ, pow_zero, rfl.le
-/
theorem le_comap_pow (n : Nat) : K.comap f ^ n <= (K ^ n).comap f := by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [Ideal.one_eq_top]; rw [Ideal.one_eq_top]
    exact rfl.le
  | succ n n_ih =>
    rw [pow_succ]; rw [pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)

/--
lemma `disjoint_map_primeCompl_iff_comap_le` / 引理 `disjoint_map_primeCompl_iff_comap_le`

English:
lemma disjoint_map_primeCompl_iff_comap_le
  statement: {S : Type*} [Semiring S] {f : R ->+* S}
  proof: (@Set.disjoint_image_right _ _ f p.primeCompl I).trans disjoint_compl_right_iff

中文:
引理 disjoint_map_primeCompl_iff_comap_le
  结论: {S : 类型} [半环 S] {f : R ->+* S}
  证明: (@Set.disjoint_image_right _ _ f p.primeCompl I).trans disjoint_compl_right_iff

Depends on / 依赖: Set.disjoint_image_right, disjoint_compl_right_iff, disjoint_image_right, p.primeCompl, primeCompl
-/
lemma disjoint_map_primeCompl_iff_comap_le {S : Type*} [Semiring S] {f : R ->+* S}
    {p : Ideal R} {I : Ideal S} [p.IsPrime] :
    Disjoint (I : Set S) (p.primeCompl.map f) ↔ I.comap f <= p :=
  (@Set.disjoint_image_right _ _ f p.primeCompl I).trans disjoint_compl_right_iff

/--
lemma `comap_map_eq_self_iff_of_isPrime` / 引理 `comap_map_eq_self_iff_of_isPrime`

English:
lemma comap_map_eq_self_iff_of_isPrime
  statement: {S : Type*} [CommSemiring S] {f : R ->+* S}
  proof: by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_le_prime_disjoint _ _
      (disjoint_map_primeCompl_iff_comap_le.mpr hp.le)
    exact ⟨q, hq₁, le_antisymm (disjoint_map_primeCompl_iff_comap_le.mp hq₃)
      (map_le_iff_le_comap.mp hq₂)⟩
  · rintro ⟨q, hq, rfl⟩
    simp

中文:
引理 comap_map_eq_self_iff_of_isPrime
  结论: {S : 类型} [交换半环 S] {f : R ->+* S}
  证明: by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_le_prime_disjoint _ _
      (disjoint_map_primeCompl_iff_comap_le.mpr hp.le)
    exact ⟨q, hq₁, le_antisymm (disjoint_map_primeCompl_iff_comap_le.mp hq₃)
      (map_le_iff_le_comap.mp hq₂)⟩
  · rintro ⟨q, hq, rfl⟩
    simp

Depends on / 依赖: Ideal.exists_le_prime_disjoint, disjoint_map_primeCompl_iff_comap_le, disjoint_map_primeCompl_iff_comap_le.mp, disjoint_map_primeCompl_iff_comap_le.mpr, exists_le_prime_disjoint, hp.le, le_antisymm, map_le_iff_le_comap, map_le_iff_le_comap.mp
-/
lemma comap_map_eq_self_iff_of_isPrime {S : Type*} [CommSemiring S] {f : R ->+* S}
    (p : Ideal R) [p.IsPrime] :
    (p.map f).comap f = p ↔ (exists (q : Ideal S), q.IsPrime ∧ q.comap f = p) := by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_le_prime_disjoint _ _
      (disjoint_map_primeCompl_iff_comap_le.mpr hp.le)
    exact ⟨q, hq₁, le_antisymm (disjoint_map_primeCompl_iff_comap_le.mp hq₃)
      (map_le_iff_le_comap.mp hq₂)⟩
  · rintro ⟨q, hq, rfl⟩
    simp

/--
theorem `comap_map_eq_self_of_isMaximal` / 定理 `comap_map_eq_self_of_isMaximal`

English:
theorem comap_map_eq_self_of_isMaximal
  statement: (f : R ->+* S) {p : Ideal R} [hP' : p.IsMaximal]
  proof: (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp le_comap_map

中文:
定理 comap_map_eq_self_of_isMaximal
  结论: (f : R ->+* S) {p : 理想 R} [hP' : p.是极大]
  证明: (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp le_comap_map

Depends on / 依赖: IsCoatom, IsCoatom.le_iff_eq, comap_ne_top, le_comap_map, le_iff_eq
-/
theorem comap_map_eq_self_of_isMaximal (f : R ->+* S) {p : Ideal R} [hP' : p.IsMaximal]
    (hP : Ideal.map f p != ⊤) : (map f p).comap f = p :=
(IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp le_comap_map

end CommRing

end MapAndComap

end Ideal

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w}

section Semiring

variable {F : Type*} {G : Type*} [Semiring R] [Semiring S] [Semiring T]
variable [FunLike F R S] [rcf : RingHomClass F R S] [FunLike G T S] [rcg : RingHomClass G T S]
variable (f : F) (g : G)

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : Ideal R
  body: Ideal.comap f ⊥

中文:
定义 ker
  签名: : 理想 R
  定义体: Ideal.comap f ⊥

Depends on / 依赖: Ideal.comap
-/
def ker : Ideal R :=
  Ideal.comap f ⊥

instance (priority := low) : (ker f).IsTwoSided := inferInstanceAs (Ideal.comap f ⊥).IsTwoSided

variable {f} in
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: {r}
  statement: r in ker f ↔ f r = 0
  proof: by rw [ker, Ideal.mem_comap, Submodule.mem_bot]

中文:
定理 mem_ker
  条件: {r}
  结论: r in ker f ↔ f r = 0
  证明: by rw [ker, Ideal.mem_comap, Submodule.mem_bot]
-/
@[simp] theorem mem_ker {r} : r in ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]

/--
theorem `ker_eq` / 定理 `ker_eq`

English:
theorem ker_eq
  statement: (ker f : Set R) = Set.preimage f {0}
  proof: rfl

中文:
定理 ker_eq
  结论: (ker f : 集合 R) = 集合.原像 f {0}
  证明: rfl
-/
theorem ker_eq : (ker f : Set R) = Set.preimage f {0} :=
  rfl

/--
theorem `ker_eq_comap_bot` / 定理 `ker_eq_comap_bot`

English:
theorem ker_eq_comap_bot
  given: (f : F)
  statement: ker f = Ideal.comap f ⊥
  proof: rfl

中文:
定理 ker_eq_comap_bot
  条件: (f : F)
  结论: ker f = 理想.comap f ⊥
  证明: rfl
-/
theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl

/--
theorem `comap_ker` / 定理 `comap_ker`

English:
theorem comap_ker
  given: (f : S ->+* R) (g : T ->+* S)
  statement: (ker f).comap g = ker (f.comp g)
  proof: by
  rw [RingHom.ker_eq_comap_bot]; rw [Ideal.comap_comap]; rw [RingHom.ker_eq_comap_bot]

中文:
定理 comap_ker
  条件: (f : S ->+* R) (g : T ->+* S)
  结论: (ker f).comap g = ker (f.comp g)
  证明: by
  rw [RingHom.ker_eq_comap_bot]; rw [Ideal.comap_comap]; rw [RingHom.ker_eq_comap_bot]

Depends on / 依赖: Ideal.comap_comap, RingHom, RingHom.ker_eq_comap_bot, comap_comap, ker_eq_comap_bot
-/
theorem comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).comap g = ker (f.comp g) := by
  rw [RingHom.ker_eq_comap_bot]; rw [Ideal.comap_comap]; rw [RingHom.ker_eq_comap_bot]

/--
theorem `one_notMem_ker` / 定理 `one_notMem_ker`

English:
theorem one_notMem_ker
  given: [Nontrivial S] (f : F)
  statement: (1 : R) ∉ ker f
  proof: by
  rw [mem_ker]; rw [map_one]
  exact one_ne_zero

中文:
定理 one_notMem_ker
  条件: [非平凡 S] (f : F)
  结论: (1 : R) ∉ ker f
  证明: by
  rw [mem_ker]; rw [map_one]
  exact one_ne_zero

Depends on / 依赖: map_one, mem_ker, one_ne_zero
-/
theorem one_notMem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker]; rw [map_one]
  exact one_ne_zero

/--
theorem `ker_ne_top` / 定理 `ker_ne_top`

English:
theorem ker_ne_top
  given: [Nontrivial S] (f : F)
  statement: ker f != ⊤
  proof: (Ideal.ne_top_iff_one _).mpr one_notMem_ker f

中文:
定理 ker_ne_top
  条件: [非平凡 S] (f : F)
  结论: ker f != ⊤
  证明: (Ideal.ne_top_iff_one _).mpr one_notMem_ker f

Depends on / 依赖: Ideal.ne_top_iff_one, ne_top_iff_one, one_notMem_ker
-/
theorem ker_ne_top [Nontrivial S] (f : F) : ker f != ⊤ :=
(Ideal.ne_top_iff_one _).mpr one_notMem_ker f

/--
lemma `ker_eq_top_of_subsingleton` / 引理 `ker_eq_top_of_subsingleton`

English:
lemma ker_eq_top_of_subsingleton
  given: [Subsingleton S] (f : F)
  statement: ker f = ⊤
  proof: eq_top_iff.mpr fun _ _ => Subsingleton.elim _ _

中文:
引理 ker_eq_top_of_subsingleton
  条件: [子单例 S] (f : F)
  结论: ker f = ⊤
  证明: eq_top_iff.mpr fun _ _ => Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, eq_top_iff, eq_top_iff.mpr
-/
lemma ker_eq_top_of_subsingleton [Subsingleton S] (f : F) : ker f = ⊤ :=
  eq_top_iff.mpr fun _ _ => Subsingleton.elim _ _

/--
lemma `_root_.Pi.ker_ringHom` / 引理 `_root_.Pi.ker_ringHom`

English:
lemma _root_.Pi.ker_ringHom
  statement: {ι : Type*} {R : ι -> Type*} [forall i, Semiring (R i)]
  proof: by
  ext x
  simp [mem_ker, funext_iff]

@[simp]

中文:
引理 _root_.依赖函数类型.ker_ringHom
  结论: {ι : 类型} {R : ι -> 类型} [对任意 i, 半环 (R i)]
  证明: by
  ext x
  simp [mem_ker, funext_iff]

@[simp]

Depends on / 依赖: funext_iff, mem_ker
-/
lemma _root_.Pi.ker_ringHom {ι : Type*} {R : ι -> Type*} [forall i, Semiring (R i)]
    (φ : forall i, S ->+* R i) : ker (RingHom.pi φ) = ⨅ i, ker (φ i) := by
  ext x
  simp [mem_ker, funext_iff]

@[simp]
/--
theorem `ker_rangeSRestrict` / 定理 `ker_rangeSRestrict`

English:
theorem ker_rangeSRestrict
  given: (f : R ->+* S)
  statement: ker f.rangeSRestrict = ker f
  proof: Ideal.ext fun _ => Subtype.ext_iff

@[simp]

中文:
定理 ker_rangeSRestrict
  条件: (f : R ->+* S)
  结论: ker f.rangeSRestrict = ker f
  证明: Ideal.ext fun _ => Subtype.ext_iff

@[simp]

Depends on / 依赖: Ideal.ext, Subtype, Subtype.ext_iff, ext_iff
-/
theorem ker_rangeSRestrict (f : R ->+* S) : ker f.rangeSRestrict = ker f :=
  Ideal.ext fun _ => Subtype.ext_iff

@[simp]
/--
theorem `ker_coe_equiv` / 定理 `ker_coe_equiv`

English:
theorem ker_coe_equiv
  given: (f : R ≃+* S)
  statement: ker (f : R ->+* S) = ⊥
  proof: by
  ext; simp

中文:
定理 ker_coe_equiv
  条件: (f : R ≃+* S)
  结论: ker (f : R ->+* S) = ⊥
  证明: by
  ext; simp
-/
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) = ⊥ := by
  ext; simp

/--
theorem `ker_coe_toRingHom` / 定理 `ker_coe_toRingHom`

English:
theorem ker_coe_toRingHom
  statement: ker (f : R ->+* S) = ker f
  proof: rfl

@[simp]

中文:
定理 ker_coe_toRingHom
  结论: ker (f : R ->+* S) = ker f
  证明: rfl

@[simp]
-/
theorem ker_coe_toRingHom : ker (f : R ->+* S) = ker f := rfl

@[simp]
/--
theorem `ker_equiv` / 定理 `ker_equiv`

English:
theorem ker_equiv
  given: {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F')
  proof: by
  ext; simp

中文:
定理 ker_equiv
  条件: {F' : 类型} [等价状 F' R S] [环等价类 F' R S] (f : F')
  证明: by
  ext; simp
-/
theorem ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F') :
    ker f = ⊥ := by
  ext; simp

/--
lemma `ker_equiv_comp` / 引理 `ker_equiv_comp`

English:
lemma ker_equiv_comp
  given: (f : R ->+* S) (e : S ≃+* T)
  proof: by
  rw [← RingHom.comap_ker]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingHom.ker_coe_equiv]; rw [RingHom.ker]

中文:
引理 ker_equiv_comp
  条件: (f : R ->+* S) (e : S ≃+* T)
  证明: by
  rw [← RingHom.comap_ker]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingHom.ker_coe_equiv]; rw [RingHom.ker]

Depends on / 依赖: RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.comap_ker, RingHom.ker, RingHom.ker_coe_equiv, comap_ker, ker_coe_equiv, toRingHom_eq_coe
-/
lemma ker_equiv_comp (f : R ->+* S) (e : S ≃+* T) :
    ker (e.toRingHom.comp f) = RingHom.ker f := by
  rw [← RingHom.comap_ker]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingHom.ker_coe_equiv]; rw [RingHom.ker]

end Semiring

section Ring

variable {F : Type*} [Ring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

/--
theorem `injective_iff_ker_eq_bot` / 定理 `injective_iff_ker_eq_bot`

English:
theorem injective_iff_ker_eq_bot
  statement: Function.Injective f ↔ ker f = ⊥
  proof: by
  rw [SetLike.ext'_iff]; rw [ker_eq]; rw [Set.ext_iff]
  exact injective_iff_map_eq_zero' f

中文:
定理 injective_iff_ker_eq_bot
  结论: 函数.单射 f ↔ ker f = ⊥
  证明: by
  rw [SetLike.ext'_iff]; rw [ker_eq]; rw [Set.ext_iff]
  exact injective_iff_map_eq_zero' f

Depends on / 依赖: Quot.mk, Set.ext_iff, SetLike, SetLike.ext, _iff, coinduced, ext_iff, injective_iff_map_eq_zero, ker_eq
-/
theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff]; rw [ker_eq]; rw [Set.ext_iff]
  exact injective_iff_map_eq_zero' f

/--
theorem `ker_eq_bot_iff_eq_zero` / 定理 `ker_eq_bot_iff_eq_zero`

English:
theorem ker_eq_bot_iff_eq_zero
  statement: ker f = ⊥ ↔ forall x, f x = 0 -> x = 0
  proof: by
  rw [← injective_iff_map_eq_zero f]; rw [injective_iff_ker_eq_bot]

中文:
定理 ker_eq_bot_iff_eq_zero
  结论: ker f = ⊥ ↔ 对任意 x, f x = 0 -> x = 0
  证明: by
  rw [← injective_iff_map_eq_zero f]; rw [injective_iff_ker_eq_bot]

Depends on / 依赖: injective_iff_ker_eq_bot, injective_iff_map_eq_zero
-/
theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ forall x, f x = 0 -> x = 0 := by
  rw [← injective_iff_map_eq_zero f]; rw [injective_iff_ker_eq_bot]

/--
lemma `ker_comp_of_injective` / 引理 `ker_comp_of_injective`

English:
lemma ker_comp_of_injective
  given: [Semiring T] (g : T ->+* R) {f : R ->+* S} (hf : Function.Injective f)
  proof: by
  rw [← RingHom.comap_ker]; rw [(injective_iff_ker_eq_bot f).mp hf]; rw [RingHom.ker]

中文:
引理 ker_comp_of_injective
  条件: [半环 T] (g : T ->+* R) {f : R ->+* S} (hf : 函数.单射 f)
  证明: by
  rw [← RingHom.comap_ker]; rw [(injective_iff_ker_eq_bot f).mp hf]; rw [RingHom.ker]

Depends on / 依赖: RingHom, RingHom.comap_ker, RingHom.ker, comap_ker, injective_iff_ker_eq_bot
-/
lemma ker_comp_of_injective [Semiring T] (g : T ->+* R) {f : R ->+* S} (hf : Function.Injective f) :
    ker (f.comp g) = RingHom.ker g := by
  rw [← RingHom.comap_ker]; rw [(injective_iff_ker_eq_bot f).mp hf]; rw [RingHom.ker]

/--
theorem `_root_.AlgHom.ker_coe_equiv` / 定理 `_root_.AlgHom.ker_coe_equiv`

English:
theorem _root_.AlgHom.ker_coe_equiv
  statement: {R A B : Type*} [CommSemiring R] [Semiring A]
  proof: RingHom.ker_coe_equiv (e.toRingEquiv)

中文:
定理 _root_.代数态射.ker_coe_equiv
  结论: {R A B : 类型} [交换半环 R] [半环 A]
  证明: RingHom.ker_coe_equiv (e.toRingEquiv)
-/
@[simp] theorem _root_.AlgHom.ker_coe_equiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    RingHom.ker (e : A ->+* B) = ⊥ :=
  RingHom.ker_coe_equiv (e.toRingEquiv)

end Ring

section RingRing

variable {F : Type*} [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

/--
theorem `sub_mem_ker_iff` / 定理 `sub_mem_ker_iff`

English:
theorem sub_mem_ker_iff
  given: {x y}
  statement: x - y in ker f ↔ f x = f y
  proof: by rw [mem_ker, map_sub, sub_eq_zero]

@[simp]

中文:
定理 sub_mem_ker_iff
  条件: {x y}
  结论: x - y in ker f ↔ f x = f y
  证明: by rw [mem_ker, map_sub, sub_eq_zero]

@[simp]

Depends on / 依赖: map_sub, mem_ker, sub_eq_zero
-/
theorem sub_mem_ker_iff {x y} : x - y in ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]

@[simp]
/--
theorem `ker_rangeRestrict` / 定理 `ker_rangeRestrict`

English:
theorem ker_rangeRestrict
  given: (f : R ->+* S)
  statement: ker f.rangeRestrict = ker f
  proof: Ideal.ext fun _ => Subtype.ext_iff

中文:
定理 ker_rangeRestrict
  条件: (f : R ->+* S)
  结论: ker f.rangeRestrict = ker f
  证明: Ideal.ext fun _ => Subtype.ext_iff

Depends on / 依赖: Ideal.ext, Subtype, Subtype.ext_iff, ext_iff
-/
theorem ker_rangeRestrict (f : R ->+* S) : ker f.rangeRestrict = ker f :=
  Ideal.ext fun _ => Subtype.ext_iff

end RingRing

/--
theorem `ker_isPrime` / 定理 `ker_isPrime`

English:
theorem ker_isPrime
  statement: {F : Type*} [Semiring R] [Semiring S] [IsDomain S]
  proof: inferInstanceAs (Ideal.comap f ⊥).IsPrime

中文:
定理 ker_isPrime
  结论: {F : 类型} [半环 R] [半环 S] [是整环 S]
  证明: inferInstanceAs (Ideal.comap f ⊥).IsPrime

Depends on / 依赖: Ideal.comap, IsPrime
-/
theorem ker_isPrime {F : Type*} [Semiring R] [Semiring S] [IsDomain S]
    [FunLike F R S] [RingHomClass F R S] (f : F) :
    (ker f).IsPrime :=
  inferInstanceAs (Ideal.comap f ⊥).IsPrime

/--
theorem `ker_isMaximal_of_surjective` / 定理 `ker_isMaximal_of_surjective`

English:
theorem ker_isMaximal_of_surjective
  statement: {R K F : Type*} [Ring R] [DivisionRing K]
  proof: have := Ideal.bot_isMaximal (K := K)
  Ideal.comap_isMaximal_of_surjective _ hf

中文:
定理 ker_isMaximal_of_surjective
  结论: {R K F : 类型} [环 R] [除环 K]
  证明: have := Ideal.bot_isMaximal (K := K)
  Ideal.comap_isMaximal_of_surjective _ hf

Depends on / 依赖: Ideal.bot_isMaximal, Ideal.comap_isMaximal_of_surjective, bot_isMaximal, comap_isMaximal_of_surjective
-/
theorem ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [DivisionRing K]
    [FunLike F R K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal :=
  have := Ideal.bot_isMaximal (K := K)
  Ideal.comap_isMaximal_of_surjective _ hf

end RingHom

section annihilator

section Semiring

variable {R M M' : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (R M) in
/--
Definition of `Module.annihilator` / `Module.annihilator` 的定义

English:
definition Module.annihilator
  signature: : Ideal R
  body: RingHom.ker (Module.toAddMonoidEnd R M)

中文:
定义 模.annihilator
  签名: : 理想 R
  定义体: RingHom.ker (Module.toAddMonoidEnd R M)

Depends on / 依赖: Module, Module.toAddMonoidEnd, RingHom, RingHom.ker, toAddMonoidEnd
-/
def Module.annihilator : Ideal R := RingHom.ker (Module.toAddMonoidEnd R M)

/--
theorem `Module.mem_annihilator` / 定理 `Module.mem_annihilator`

English:
theorem Module.mem_annihilator
  given: {r}
  statement: r in Module.annihilator R M ↔ forall m : M, r • m = 0
  proof: ⟨fun h => (congr($h ·)), (AddMonoidHom.ext ·)⟩

中文:
定理 模.mem_annihilator
  条件: {r}
  结论: r in 模.annihilator R M ↔ 对任意 m : M, r • m = 0
  证明: ⟨fun h => (congr($h ·)), (AddMonoidHom.ext ·)⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext
-/
theorem Module.mem_annihilator {r} : r in Module.annihilator R M ↔ forall m : M, r • m = 0 :=
  ⟨fun h => (congr($h ·)), (AddMonoidHom.ext ·)⟩

/--
lemma `Module.mem_annihilator_iff_lsmul_eq_zero` / 引理 `Module.mem_annihilator_iff_lsmul_eq_zero`

English:
lemma Module.mem_annihilator_iff_lsmul_eq_zero
  statement: {R : Type*} [CommSemiring R]
  proof: by
  simp [Module.mem_annihilator, LinearMap.ext_iff]

中文:
引理 模.mem_annihilator_iff_lsmul_eq_zero
  结论: {R : 类型} [交换半环 R]
  证明: by
  simp [Module.mem_annihilator, LinearMap.ext_iff]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, Module, Module.mem_annihilator, ext_iff, mem_annihilator
-/
lemma Module.mem_annihilator_iff_lsmul_eq_zero {R : Type*} [CommSemiring R]
    [Module R M] {r : R} : r in Module.annihilator R M ↔ LinearMap.lsmul R M r = 0 := by
  simp [Module.mem_annihilator, LinearMap.ext_iff]

instance (priority := low) : (Module.annihilator R M).IsTwoSided :=
  inferInstanceAs (RingHom.ker _).IsTwoSided

/--
theorem `LinearMap.annihilator_le_of_injective` / 定理 `LinearMap.annihilator_le_of_injective`

English:
theorem LinearMap.annihilator_le_of_injective
  given: (f : M ->ₗ[R] M') (hf : Function.Injective f)
  proof: fun x h => by
  rw [Module.mem_annihilator] at h ⊢; exact fun m => hf (by rw [map_smul, h, f.map_zero])

中文:
定理 线性映射.annihilator_le_of_injective
  条件: (f : M ->ₗ[R] M') (hf : 函数.单射 f)
  证明: fun x h => by
  rw [Module.mem_annihilator] at h ⊢; exact fun m => hf (by rw [map_smul, h, f.map_zero])

Depends on / 依赖: Module, Module.mem_annihilator, f.map_zero, map_smul, map_zero, mem_annihilator
-/
theorem LinearMap.annihilator_le_of_injective (f : M ->ₗ[R] M') (hf : Function.Injective f) :
    Module.annihilator R M' <= Module.annihilator R M := fun x h => by
  rw [Module.mem_annihilator] at h ⊢; exact fun m => hf (by rw [map_smul, h, f.map_zero])

/--
theorem `LinearMap.annihilator_le_of_surjective` / 定理 `LinearMap.annihilator_le_of_surjective`

English:
theorem LinearMap.annihilator_le_of_surjective
  statement: (f : M ->ₗ[R] M')
  proof: fun x h => by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul]; rw [h]; rw [f.map_zero]

中文:
定理 线性映射.annihilator_le_of_surjective
  结论: (f : M ->ₗ[R] M')
  证明: fun x h => by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul]; rw [h]; rw [f.map_zero]

Depends on / 依赖: Module, Module.mem_annihilator, f.map_zero, map_smul, map_zero, mem_annihilator
-/
theorem LinearMap.annihilator_le_of_surjective (f : M ->ₗ[R] M')
    (hf : Function.Surjective f) : Module.annihilator R M <= Module.annihilator R M' := fun x h => by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul]; rw [h]; rw [f.map_zero]

/--
theorem `LinearEquiv.annihilator_eq` / 定理 `LinearEquiv.annihilator_eq`

English:
theorem LinearEquiv.annihilator_eq
  given: (e : M ≃ₗ[R] M')
  proof: (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

中文:
定理 线性等价.annihilator_eq
  条件: (e : M ≃ₗ[R] M')
  证明: (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

Depends on / 依赖: annihilator_le_of_injective, annihilator_le_of_surjective, antisymm, e.annihilator_le_of_injective, e.annihilator_le_of_surjective, e.injective, e.surjective, injective, surjective
-/
theorem LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') :
    Module.annihilator R M = Module.annihilator R M' :=
  (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

/--
theorem `Module.comap_annihilator` / 定理 `Module.comap_annihilator`

English:
theorem Module.comap_annihilator
  statement: {R₀} [CommSemiring R₀] [Module R₀ M]
  proof: by
  ext x
  simp [mem_annihilator]

中文:
定理 模.comap_annihilator
  结论: {R₀} [交换半环 R₀] [模 R₀ M]
  证明: by
  ext x
  simp [mem_annihilator]

Depends on / 依赖: mem_annihilator
-/
theorem Module.comap_annihilator {R₀} [CommSemiring R₀] [Module R₀ M]
    [Algebra R₀ R] [IsScalarTower R₀ R M] :
    (Module.annihilator R M).comap (algebraMap R₀ R) = Module.annihilator R₀ M := by
  ext x
  simp [mem_annihilator]

/--
lemma `Module.annihilator_eq_bot` / 引理 `Module.annihilator_eq_bot`

English:
lemma Module.annihilator_eq_bot
  given: {R M} [Ring R] [AddCommGroup M] [Module R M]
  proof: by
  rw [← le_bot_iff]
  refine ⟨fun H => ⟨fun {r s} H' => ?_⟩, fun ⟨H⟩ {a} ha => ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])

中文:
引理 模.annihilator_eq_bot
  条件: {R M} [环 R] [加法交换群 M] [模 R M]
  证明: by
  rw [← le_bot_iff]
  refine ⟨fun H => ⟨fun {r s} H' => ?_⟩, fun ⟨H⟩ {a} ha => ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])

Depends on / 依赖: Module, Module.mem_annihilator, Module.mem_annihilator.mp, implies_true, le_bot_iff, mem_annihilator, sub_eq_zero, sub_self, sub_smul
-/
lemma Module.annihilator_eq_bot {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module.annihilator R M = ⊥ ↔ FaithfulSMul R M := by
  rw [← le_bot_iff]
  refine ⟨fun H => ⟨fun {r s} H' => ?_⟩, fun ⟨H⟩ {a} ha => ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])

/--
theorem `Module.annihilator_eq_top_iff` / 定理 `Module.annihilator_eq_top_iff`

English:
theorem Module.annihilator_eq_top_iff
  statement: annihilator R M = ⊤ ↔ Subsingleton M
  proof: ⟨fun h => ⟨fun m m' => by
      rw [← one_smul R m]; rw [← one_smul R m']
      simp_rw [mem_annihilator.mp (h ▸ Submodule.mem_top)]⟩,
    fun _ => top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => Subsingleton.elim _ _⟩

中文:
定理 模.annihilator_eq_top_iff
  结论: annihilator R M = ⊤ ↔ 子单例 M
  证明: ⟨fun h => ⟨fun m m' => by
      rw [← one_smul R m]; rw [← one_smul R m']
      simp_rw [mem_annihilator.mp (h ▸ Submodule.mem_top)]⟩,
    fun _ => top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => Subsingleton.elim _ _⟩

Depends on / 依赖: Submodule, Submodule.mem_top, Subsingleton, Subsingleton.elim, mem_annihilator, mem_annihilator.mp, mem_annihilator.mpr, mem_top, one_smul, simp_rw, top_le_iff, top_le_iff.mp
-/
theorem Module.annihilator_eq_top_iff : annihilator R M = ⊤ ↔ Subsingleton M :=
  ⟨fun h => ⟨fun m m' => by
      rw [← one_smul R m]; rw [← one_smul R m']
      simp_rw [mem_annihilator.mp (h ▸ Submodule.mem_top)]⟩,
    fun _ => top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => Subsingleton.elim _ _⟩

/--
theorem `Module.annihilator_prod` / 定理 `Module.annihilator_prod`

English:
theorem Module.annihilator_prod
  statement: annihilator R (M × M') = annihilator R M ⊓ annihilator R M'
  proof: by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]

中文:
定理 模.annihilator_prod
  结论: annihilator R (M × M') = annihilator R M ⊓ annihilator R M'
  证明: by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]

Depends on / 依赖: Ideal.mem_inf, Prod.forall, Prod.mk_eq_zero, Prod.smul_mk, forall_and_left, forall_and_right, mem_annihilator, mem_inf, mk_eq_zero, simp_rw, smul_mk
-/
theorem Module.annihilator_prod : annihilator R (M × M') = annihilator R M ⊓ annihilator R M' := by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]

/--
theorem `Module.annihilator_finsupp` / 定理 `Module.annihilator_finsupp`

English:
theorem Module.annihilator_finsupp
  given: {ι : Type*} [Nonempty ι]
  proof: by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · refine Nonempty.elim ‹_› fun i : ι => ?_
    simpa using fun m => congr($(h (Finsupp.single i m)) i)
  · intro m; ext i; exact h _

中文:
定理 模.annihilator_finsupp
  条件: {ι : 类型} [非空 ι]
  证明: by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · refine Nonempty.elim ‹_› fun i : ι => ?_
    simpa using fun m => congr($(h (Finsupp.single i m)) i)
  · intro m; ext i; exact h _

Depends on / 依赖: Finsupp, Finsupp.single, Nonempty, Nonempty.elim, mem_annihilator, simp_rw, single
-/
theorem Module.annihilator_finsupp {ι : Type*} [Nonempty ι] :
    annihilator R (ι ->₀ M) = annihilator R M := by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · refine Nonempty.elim ‹_› fun i : ι => ?_
    simpa using fun m => congr($(h (Finsupp.single i m)) i)
  · intro m; ext i; exact h _

section

variable {ι : Type*} {M : ι -> Type*} [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]

/--
theorem `Module.annihilator_dfinsupp` / 定理 `Module.annihilator_dfinsupp`

English:
theorem Module.annihilator_dfinsupp
  statement: annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i)
  proof: by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _

中文:
定理 模.annihilator_dfinsupp
  结论: annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i)
  证明: by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _

Depends on / 依赖: DFinsupp, DFinsupp.single, DFunLike, DFunLike.congr_fun, Ideal.mem_iInf, classical, congr_fun, mem_annihilator, mem_iInf, single
-/
theorem Module.annihilator_dfinsupp : annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _

/--
theorem `Module.annihilator_pi` / 定理 `Module.annihilator_pi`

English:
theorem Module.annihilator_pi
  statement: annihilator R (Π i, M i) = ⨅ i, annihilator R (M i)
  proof: by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

中文:
定理 模.annihilator_pi
  结论: annihilator R (Π i, M i) = ⨅ i, annihilator R (M i)
  证明: by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

Depends on / 依赖: Ideal.mem_iInf, Pi.single, classical, congr_fun, mem_annihilator, mem_iInf, single
-/
theorem Module.annihilator_pi : annihilator R (Π i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

end

namespace Submodule

/--
Definition of `annihilator` / `annihilator` 的定义

English:
abbreviation annihilator
  signature: (N : Submodule R M)
  body: Module.annihilator R N

中文:
缩写 annihilator
  签名: (N : 子模 R M)
  定义体: Module.annihilator R N

Depends on / 依赖: Module, Module.annihilator, annihilator
-/
abbrev annihilator (N : Submodule R M) : Ideal R :=
  Module.annihilator R N

/--
theorem `annihilator_top` / 定理 `annihilator_top`

English:
theorem annihilator_top
  statement: (⊤ : Submodule R M).annihilator = Module.annihilator R M
  proof: topEquiv.annihilator_eq

中文:
定理 annihilator_top
  结论: (⊤ : 子模 R M).annihilator = 模.annihilator R M
  证明: topEquiv.annihilator_eq

Depends on / 依赖: annihilator_eq, topEquiv, topEquiv.annihilator_eq
-/
theorem annihilator_top : (⊤ : Submodule R M).annihilator = Module.annihilator R M :=
  topEquiv.annihilator_eq

variable {I J : Ideal R} {N P : Submodule R M}

/--
theorem `mem_annihilator` / 定理 `mem_annihilator`

English:
theorem mem_annihilator
  given: {r}
  statement: r in N.annihilator ↔ forall n in N, r • n = (0 : M)
  proof: by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl

中文:
定理 mem_annihilator
  条件: {r}
  结论: r in N.annihilator ↔ 对任意 n in N, r • n = (0 : M)
  证明: by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl

Depends on / 依赖: Module, Module.mem_annihilator, Subtype, Subtype.ext_iff, Subtype.forall, annihilator, ext_iff, mem_annihilator, simp_rw
-/
theorem mem_annihilator {r} : r in N.annihilator ↔ forall n in N, r • n = (0 : M) := by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl

/--
theorem `annihilator_bot` / 定理 `annihilator_bot`

English:
theorem annihilator_bot
  statement: (⊥ : Submodule R M).annihilator = ⊤
  proof: top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => by rintro rfl; rw [smul_zero]

中文:
定理 annihilator_bot
  结论: (⊥ : 子模 R M).annihilator = ⊤
  证明: top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => by rintro rfl; rw [smul_zero]

Depends on / 依赖: mem_annihilator, mem_annihilator.mpr, smul_zero, top_le_iff, top_le_iff.mp
-/
theorem annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤ :=
  top_le_iff.mp fun _ _ => mem_annihilator.mpr fun _ => by rintro rfl; rw [smul_zero]

/--
theorem `annihilator_eq_top_iff` / 定理 `annihilator_eq_top_iff`

English:
theorem annihilator_eq_top_iff
  statement: N.annihilator = ⊤ ↔ N = ⊥
  proof: by
  rw [annihilator]; rw [Module.annihilator_eq_top_iff]; rw [Submodule.subsingleton_iff_eq_bot]

中文:
定理 annihilator_eq_top_iff
  结论: N.annihilator = ⊤ ↔ N = ⊥
  证明: by
  rw [annihilator]; rw [Module.annihilator_eq_top_iff]; rw [Submodule.subsingleton_iff_eq_bot]

Depends on / 依赖: Module, Module.annihilator_eq_top_iff, Submodule, Submodule.subsingleton_iff_eq_bot, annihilator, annihilator_eq_top_iff, subsingleton_iff_eq_bot
-/
theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ := by
  rw [annihilator]; rw [Module.annihilator_eq_top_iff]; rw [Submodule.subsingleton_iff_eq_bot]

/--
theorem `annihilator_mono` / 定理 `annihilator_mono`

English:
theorem annihilator_mono
  given: (h : N <= P)
  statement: P.annihilator <= N.annihilator
  proof: fun _ hrp =>
mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n h hn

中文:
定理 annihilator_mono
  条件: (h : N <= P)
  结论: P.annihilator <= N.annihilator
  证明: fun _ hrp =>
mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n h hn
-/
theorem annihilator_mono (h : N <= P) : P.annihilator <= N.annihilator := fun _ hrp =>
mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n h hn

/--
theorem `annihilator_iSup` / 定理 `annihilator_iSup`

English:
theorem annihilator_iSup
  given: (ι : Sort w) (f : ι -> Submodule R M)
  proof: le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun r H =>
    mem_annihilator.2 fun n hn => iSup_induction f (motive := (r • · = 0)) hn
      (fun i => mem_annihilator.1 <| (mem_iInf _).mp H i) (smul_zero _)
      fun m₁ m₂ h₁ h₂ => by simp_rw [smul_add, h₁, h₂, add_zero]

中文:
定理 annihilator_iSup
  条件: (ι : 类型层 w) (f : ι -> 子模 R M)
  证明: le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun r H =>
    mem_annihilator.2 fun n hn => iSup_induction f (motive := (r • · = 0)) hn
      (fun i => mem_annihilator.1 <| (mem_iInf _).mp H i) (smul_zero _)
      fun m₁ m₂ h₁ h₂ => by simp_rw [smul_add, h₁, h₂, add_zero]

Depends on / 依赖: add_zero, annihilator_mono, iSup_induction, le_antisymm, le_iInf, le_iSup, mem_annihilator, mem_iInf, motive, simp_rw, smul_add, smul_zero
-/
theorem annihilator_iSup (ι : Sort w) (f : ι -> Submodule R M) :
    annihilator (⨆ i, f i) = ⨅ i, annihilator (f i) :=
  le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun r H =>
    mem_annihilator.2 fun n hn => iSup_induction f (motive := (r • · = 0)) hn
      (fun i => mem_annihilator.1 <| (mem_iInf _).mp H i) (smul_zero _)
      fun m₁ m₂ h₁ h₂ => by simp_rw [smul_add, h₁, h₂, add_zero]

/--
theorem `annihilator_sup` / 定理 `annihilator_sup`

English:
theorem annihilator_sup
  given: (N P : Submodule R M)
  proof: by
  rw [← sSup_pair]; rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [annihilator_iSup]; rw [← iInf_pair]; rw [iInf_subtype']

中文:
定理 annihilator_sup
  条件: (N P : 子模 R M)
  证明: by
  rw [← sSup_pair]; rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [annihilator_iSup]; rw [← iInf_pair]; rw [iInf_subtype']

Depends on / 依赖: annihilator_iSup, iInf_pair, iInf_subtype, iSup_subtype, sSup_eq_iSup, sSup_pair
-/
theorem annihilator_sup (N P : Submodule R M) :
    (N ⊔ P).annihilator = N.annihilator ⊓ P.annihilator := by
  rw [← sSup_pair]; rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [annihilator_iSup]; rw [← iInf_pair]; rw [iInf_subtype']

/--
theorem `le_annihilator_iff` / 定理 `le_annihilator_iff`

English:
theorem le_annihilator_iff
  given: {N : Submodule R M} {I : Ideal R}
  statement: I <= annihilator N ↔ I • N = ⊥
  proof: by
  simp_rw [← le_bot_iff, smul_le, SetLike.le_def, mem_annihilator]; rfl

@[simp]

中文:
定理 le_annihilator_iff
  条件: {N : 子模 R M} {I : 理想 R}
  结论: I <= annihilator N ↔ I • N = ⊥
  证明: by
  simp_rw [← le_bot_iff, smul_le, SetLike.le_def, mem_annihilator]; rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.le_def, le_bot_iff, le_def, mem_annihilator, simp_rw, smul_le
-/
theorem le_annihilator_iff {N : Submodule R M} {I : Ideal R} : I <= annihilator N ↔ I • N = ⊥ := by
  simp_rw [← le_bot_iff, smul_le, SetLike.le_def, mem_annihilator]; rfl

@[simp]
/--
theorem `annihilator_smul` / 定理 `annihilator_smul`

English:
theorem annihilator_smul
  given: (N : Submodule R M)
  statement: annihilator N • N = ⊥
  proof: eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)

@[simp]

中文:
定理 annihilator_smul
  条件: (N : 子模 R M)
  结论: annihilator N • N = ⊥
  证明: eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)

@[simp]

Depends on / 依赖: eq_bot_iff, mem_annihilator, smul_le
-/
theorem annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥ :=
  eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)

@[simp]
/--
theorem `annihilator_mul` / 定理 `annihilator_mul`

English:
theorem annihilator_mul
  given: (I : Ideal R)
  statement: annihilator I * I = ⊥
  proof: annihilator_smul I

中文:
定理 annihilator_mul
  条件: (I : 理想 R)
  结论: annihilator I * I = ⊥
  证明: annihilator_smul I

Depends on / 依赖: annihilator_smul
-/
theorem annihilator_mul (I : Ideal R) : annihilator I * I = ⊥ :=
  annihilator_smul I

end Submodule

end Semiring

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Submodule R M}

/--
theorem `mem_annihilator'` / 定理 `mem_annihilator'`

English:
theorem mem_annihilator'
  given: {r}
  statement: r in N.annihilator ↔ N <= comap (r • (LinearMap.id : M ->ₗ[R] M)) ⊥
  proof: mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 H n hn, fun H _ hn => (mem_bot R).1 H hn⟩

中文:
定理 mem_annihilator'
  条件: {r}
  结论: r in N.annihilator ↔ N <= comap (r • (线性映射.id : M ->ₗ[R] M)) ⊥
  证明: mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 H n hn, fun H _ hn => (mem_bot R).1 H hn⟩

Depends on / 依赖: mem_annihilator, mem_annihilator.trans, mem_bot
-/
theorem mem_annihilator' {r} : r in N.annihilator ↔ N <= comap (r • (LinearMap.id : M ->ₗ[R] M)) ⊥ :=
mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 H n hn, fun H _ hn => (mem_bot R).1 H hn⟩

/--
theorem `mem_annihilator_span` / 定理 `mem_annihilator_span`

English:
theorem mem_annihilator_span
  given: (s : Set M) (r : R)
  proof: by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add]; rw [hx]; rw [hy]; rw [zero_add]
    · intro a x _ hx
      rw [smul_comm]; rw [hx]; rw [smul_zero]

中文:
定理 mem_annihilator_span
  条件: (s : 集合 M) (r : R)
  证明: by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add]; rw [hx]; rw [hy]; rw [zero_add]
    · intro a x _ hx
      rw [smul_comm]; rw [hx]; rw [smul_zero]

Depends on / 依赖: Submodule, Submodule.mem_annihilator, Submodule.span_induction, Submodule.subset_span, mem_annihilator, n.prop, smul_add, smul_comm, smul_zero, span_induction, subset_span, zero_add
-/
theorem mem_annihilator_span (s : Set M) (r : R) :
    r in (Submodule.span R s).annihilator ↔ forall n : s, r • (n : M) = 0 := by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add]; rw [hx]; rw [hy]; rw [zero_add]
    · intro a x _ hx
      rw [smul_comm]; rw [hx]; rw [smul_zero]

/--
theorem `mem_annihilator_span_singleton` / 定理 `mem_annihilator_span_singleton`

English:
theorem mem_annihilator_span_singleton
  given: (g : M) (r : R)
  proof: by simp [mem_annihilator_span]

中文:
定理 mem_annihilator_span_singleton
  条件: (g : M) (r : R)
  证明: by simp [mem_annihilator_span]

Depends on / 依赖: mem_annihilator_span
-/
theorem mem_annihilator_span_singleton (g : M) (r : R) :
    r in (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0 := by simp [mem_annihilator_span]

open LinearMap in
/--
theorem `annihilator_span` / 定理 `annihilator_span`

English:
theorem annihilator_span
  given: (s : Set M)
  proof: by
  ext; simp [mem_annihilator_span]

中文:
定理 annihilator_span
  条件: (s : 集合 M)
  证明: by
  ext; simp [mem_annihilator_span]

Depends on / 依赖: mem_annihilator_span
-/
theorem annihilator_span (s : Set M) :
    (Submodule.span R s).annihilator = ⨅ g : s, ker (toSpanSingleton R M g.1) := by
  ext; simp [mem_annihilator_span]

open LinearMap in
/--
theorem `annihilator_span_singleton` / 定理 `annihilator_span_singleton`

English:
theorem annihilator_span_singleton
  given: (g : M)
  proof: by
  simp [annihilator_span]

@[simp]

中文:
定理 annihilator_span_singleton
  条件: (g : M)
  证明: by
  simp [annihilator_span]

@[simp]

Depends on / 依赖: annihilator_span
-/
theorem annihilator_span_singleton (g : M) :
    (Submodule.span R {g}).annihilator = ker (toSpanSingleton R M g) := by
  simp [annihilator_span]

@[simp]
/--
theorem `mul_annihilator` / 定理 `mul_annihilator`

English:
theorem mul_annihilator
  given: (I : Ideal R)
  statement: I * annihilator I = ⊥
  proof: by rw [mul_comm, annihilator_mul]

中文:
定理 mul_annihilator
  条件: (I : 理想 R)
  结论: I * annihilator I = ⊥
  证明: by rw [mul_comm, annihilator_mul]

Depends on / 依赖: annihilator_mul, mul_comm
-/
theorem mul_annihilator (I : Ideal R) : I * annihilator I = ⊥ := by rw [mul_comm, annihilator_mul]

/--
theorem `restrictScalars_map_smul_eq` / 定理 `restrictScalars_map_smul_eq`

English:
theorem restrictScalars_map_smul_eq
  statement: {S M : Type*}
  proof: by
  have := N.restrictScalars_image_smul_eq (I : Set S)
  rw [coe_set_smul] at this
  rw [Ideal.map]; rw [span_smul_eq]; rw [← this]

中文:
定理 restrictScalars_map_smul_eq
  结论: {S M : 类型}
  证明: by
  have := N.restrictScalars_image_smul_eq (I : Set S)
  rw [coe_set_smul] at this
  rw [Ideal.map]; rw [span_smul_eq]; rw [← this]

Depends on / 依赖: Ideal.map, N.restrictScalars_image_smul_eq, coe_set_smul, restrictScalars_image_smul_eq, span_smul_eq
-/
theorem restrictScalars_map_smul_eq {S M : Type*}
    [CommSemiring S] [Algebra S R]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]
    (I : Ideal S) (N : Submodule R M) :
    ((I.map (algebraMap S R)) • N).restrictScalars S = I • N.restrictScalars S := by
  have := N.restrictScalars_image_smul_eq (I : Set S)
  rw [coe_set_smul] at this
  rw [Ideal.map]; rw [span_smul_eq]; rw [← this]

end Submodule

end annihilator

namespace Ideal

variable {R : Type*} {S : Type*} {F : Type*}

section Semiring

variable [Semiring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S]

/--
theorem `map_eq_bot_iff_le_ker` / 定理 `map_eq_bot_iff_le_ker`

English:
theorem map_eq_bot_iff_le_ker
  given: {I : Ideal R} (f : F)
  statement: I.map f = ⊥ ↔ I <= RingHom.ker f
  proof: by
  rw [RingHom.ker]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]

中文:
定理 map_eq_bot_iff_le_ker
  条件: {I : 理想 R} (f : F)
  结论: I.map f = ⊥ ↔ I <= 环态射.ker f
  证明: by
  rw [RingHom.ker]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]

Depends on / 依赖: RingHom, RingHom.ker, eq_bot_iff, map_le_iff_le_comap
-/
theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I <= RingHom.ker f := by
  rw [RingHom.ker]; rw [eq_bot_iff]; rw [map_le_iff_le_comap]

/--
theorem `ker_le_comap` / 定理 `ker_le_comap`

English:
theorem ker_le_comap
  given: {K : Ideal S} (f : F)
  statement: RingHom.ker f <= comap f K
  proof: fun _ hx =>
  mem_comap.2 (RingHom.mem_ker.1 hx ▸ K.zero_mem)

中文:
定理 ker_le_comap
  条件: {K : 理想 S} (f : F)
  结论: 环态射.ker f <= comap f K
  证明: fun _ hx =>
  mem_comap.2 (RingHom.mem_ker.1 hx ▸ K.zero_mem)
-/
theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <= comap f K := fun _ hx =>
  mem_comap.2 (RingHom.mem_ker.1 hx ▸ K.zero_mem)

/--
Instance `map_isPrime_of_equiv` / 实例 `map_isPrime_of_equiv`

English:
instance map_isPrime_of_equiv
  signature: {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
  body: by
  have h : I.map f = I.map ((RingEquivClass.toRingEquiv f : R ≃+* S) : R ->+* S) := rfl
  rw [h]; rw [map_comap_of_equiv (RingEquivClass.toRingEquiv f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquivClass.toRingEquiv f : R ≃+* S).symm

中文:
实例 map_isPrime_of_equiv
  签名: {F' : 类型} [等价状 F' R S] [环等价类 F' R S]
  定义体: by
  have h : I.map f = I.map ((RingEquivClass.toRingEquiv f : R ≃+* S) : R ->+* S) := rfl
  rw [h]; rw [map_comap_of_equiv (RingEquivClass.toRingEquiv f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquivClass.toRingEquiv f : R ≃+* S).symm

Depends on / 依赖: I.map, Ideal.IsPrime.comap, IsPrime, RingEquivClass, RingEquivClass.toRingEquiv, map_comap_of_equiv, toRingEquiv
-/
instance map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
    (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I) := by
  have h : I.map f = I.map ((RingEquivClass.toRingEquiv f : R ≃+* S) : R ->+* S) := rfl
  rw [h]; rw [map_comap_of_equiv (RingEquivClass.toRingEquiv f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquivClass.toRingEquiv f : R ≃+* S).symm

/--
theorem `map_eq_bot_iff_of_injective` / 定理 `map_eq_bot_iff_of_injective`

English:
theorem map_eq_bot_iff_of_injective
  given: {I : Ideal R} {f : F} (hf : Function.Injective f)
  proof: by
  simp [map, ← map_zero f, -map_zero, hf.eq_iff, I.eq_bot_iff]

中文:
定理 map_eq_bot_iff_of_injective
  条件: {I : 理想 R} {f : F} (hf : 函数.单射 f)
  证明: by
  simp [map, ← map_zero f, -map_zero, hf.eq_iff, I.eq_bot_iff]

Depends on / 依赖: I.eq_bot_iff, eq_bot_iff, eq_iff, hf.eq_iff, map_zero
-/
theorem map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective f) :
    I.map f = ⊥ ↔ I = ⊥ := by
  simp [map, ← map_zero f, -map_zero, hf.eq_iff, I.eq_bot_iff]

end Semiring

open scoped Pointwise in
/--
lemma `map_pointwise_smul` / 引理 `map_pointwise_smul`

English:
lemma map_pointwise_smul
  statement: {R S : Type*} [CommSemiring R] [CommSemiring S]
  proof: by
  rw [← Submodule.ideal_span_singleton_smul]; rw [smul_eq_mul]; rw [Ideal.map_mul]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [← smul_eq_mul]; rw [Submodule.ideal_span_singleton_smul]

中文:
引理 map_pointwise_smul
  结论: {R S : 类型} [交换半环 R] [交换半环 S]
  证明: by
  rw [← Submodule.ideal_span_singleton_smul]; rw [smul_eq_mul]; rw [Ideal.map_mul]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [← smul_eq_mul]; rw [Submodule.ideal_span_singleton_smul]

Depends on / 依赖: Ideal.map_mul, Ideal.map_span, Set.image_singleton, Submodule, Submodule.ideal_span_singleton_smul, ideal_span_singleton_smul, image_singleton, map_mul, map_span, smul_eq_mul
-/
lemma map_pointwise_smul {R S : Type*} [CommSemiring R] [CommSemiring S]
    (r : R) (I : Ideal R) (f : R ->+* S) :
    Ideal.map f (r • I) = f r • I.map f := by
  rw [← Submodule.ideal_span_singleton_smul]; rw [smul_eq_mul]; rw [Ideal.map_mul]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [← smul_eq_mul]; rw [Submodule.ideal_span_singleton_smul]

section Ring

variable [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S]

/--
lemma `comap_map_of_surjective'` / 引理 `comap_map_of_surjective'`

English:
lemma comap_map_of_surjective'
  given: (f : F) (hf : Function.Surjective f) (I : Ideal R)
  proof: comap_map_of_surjective f hf I

中文:
引理 comap_map_of_surjective'
  条件: (f : F) (hf : 函数.满射 f) (I : 理想 R)
  证明: comap_map_of_surjective f hf I

Depends on / 依赖: comap_map_of_surjective
-/
lemma comap_map_of_surjective' (f : F) (hf : Function.Surjective f) (I : Ideal R) :
    (I.map f).comap f = I ⊔ RingHom.ker f :=
  comap_map_of_surjective f hf I

/--
theorem `map_sInf` / 定理 `map_sInf`

English:
theorem map_sInf
  given: {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f)
  proof: by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    obtain ⟨x, hx⟩ := (mem_map_iff_of_surjective f hf).1 hy
    obtain ⟨J, hJ⟩ := (Set.mem_image _ _ _).mp hj
    rw [← hJ.right]; rw [← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    obtain ⟨x, hx⟩ := hf y
    refine hx ▸ mem_map_of_mem f ?_
    have : forall I in A, y in map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' in J := by
      apply h J hJ
      rw [RingHom.mem_ker]; rw [map_sub]; rw [hx]; rw [sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'

中文:
定理 map_sInf
  条件: {A : 集合 (理想 R)} {f : F} (hf : 函数.满射 f)
  证明: by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    obtain ⟨x, hx⟩ := (mem_map_iff_of_surjective f hf).1 hy
    obtain ⟨J, hJ⟩ := (Set.mem_image _ _ _).mp hj
    rw [← hJ.right]; rw [← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    obtain ⟨x, hx⟩ := hf y
    refine hx ▸ mem_map_of_mem f ?_
    have : forall I in A, y in map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' in J := by
      apply h J hJ
      rw [RingHom.mem_ker]; rw [map_sub]; rw [hx]; rw [sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'

Depends on / 依赖: Set.mem_image, Submodule, Submodule.mem_sInf, hJ.left, hJ.right, hx.left, hx.right, le_antisymm, le_of_eq, le_sInf, mem_image, mem_map_iff_of_surjective, mem_map_of_mem, mem_sInf, sInf_le_of_le
-/
theorem map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (forall J in A, RingHom.ker f <= J) -> map f (sInf A) = sInf (map f '' A) := by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    obtain ⟨x, hx⟩ := (mem_map_iff_of_surjective f hf).1 hy
    obtain ⟨J, hJ⟩ := (Set.mem_image _ _ _).mp hj
    rw [← hJ.right]; rw [← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    obtain ⟨x, hx⟩ := hf y
    refine hx ▸ mem_map_of_mem f ?_
    have : forall I in A, y in map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' in J := by
      apply h J hJ
      rw [RingHom.mem_ker]; rw [map_sub]; rw [hx]; rw [sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'

/--
theorem `map_isPrime_of_surjective` / 定理 `map_isPrime_of_surjective`

English:
theorem map_isPrime_of_surjective
  statement: {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
  proof: by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf]; rw [comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha]; rw [← hb]; rw [← map_mul f]; rw [mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero]; rw [← map_sub] at hc'
    have : a * b in I := by
      convert! I.sub_mem hc (hk (hc' : c - a * b in RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h

中文:
定理 map_isPrime_of_surjective
  结论: {f : F} (hf : 函数.满射 f) {I : 理想 R} [H : 是素 I]
  证明: by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf]; rw [comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha]; rw [← hb]; rw [← map_mul f]; rw [mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero]; rw [← map_sub] at hc'
    have : a * b in I := by
      convert! I.sub_mem hc (hk (hc' : c - a * b in RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h

Depends on / 依赖: H.ne_top, I.sub_mem, RingHom, RingHom.ker, comap_map_of_surjective, comap_top, congr_arg, convert, eq_top_iff, le_of_eq, map_mul, map_sub, mem_map_iff_of_surjective, ne_top, replace, sub_eq_zero, sub_mem, sup_le
-/
theorem map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f <= I) : IsPrime (map f I) := by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf]; rw [comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha]; rw [← hb]; rw [← map_mul f]; rw [mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero]; rw [← map_sub] at hc'
    have : a * b in I := by
      convert! I.sub_mem hc (hk (hc' : c - a * b in RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h

/--
lemma `IsMaximal.map_of_surjective_of_ker_le` / 引理 `IsMaximal.map_of_surjective_of_ker_le`

English:
lemma IsMaximal.map_of_surjective_of_ker_le
  statement: {f : F} (hf : Function.Surjective f) {m : Ideal R}
  proof: by
.resolve_left fun h => ?_ refine m.map_eq_top_or_isMaximal_of_surjective f hf ‹_›
  apply congr_arg (comap f) at h
  rw [comap_map_of_surjective _ hf]; rw [comap_top]; rw [← RingHom.ker_eq_comap_bot]; rw [sup_of_le_left hk] at h
  exact IsMaximal.ne_top ‹_› h

中文:
引理 是极大.map_of_surjective_of_ker_le
  结论: {f : F} (hf : 函数.满射 f) {m : 理想 R}
  证明: by
.resolve_left fun h => ?_ refine m.map_eq_top_or_isMaximal_of_surjective f hf ‹_›
  apply congr_arg (comap f) at h
  rw [comap_map_of_surjective _ hf]; rw [comap_top]; rw [← RingHom.ker_eq_comap_bot]; rw [sup_of_le_left hk] at h
  exact IsMaximal.ne_top ‹_› h

Depends on / 依赖: IsMaximal, IsMaximal.ne_top, RingHom, RingHom.ker_eq_comap_bot, comap_map_of_surjective, comap_top, congr_arg, ker_eq_comap_bot, m.map_eq_top_or_isMaximal_of_surjective, map_eq_top_or_isMaximal_of_surjective, ne_top, resolve_left, sup_of_le_left
-/
lemma IsMaximal.map_of_surjective_of_ker_le {f : F} (hf : Function.Surjective f) {m : Ideal R}
    [m.IsMaximal] (hk : RingHom.ker f <= m) : (m.map f).IsMaximal := by
.resolve_left fun h => ?_ refine m.map_eq_top_or_isMaximal_of_surjective f hf ‹_›
  apply congr_arg (comap f) at h
  rw [comap_map_of_surjective _ hf]; rw [comap_top]; rw [← RingHom.ker_eq_comap_bot]; rw [sup_of_le_left hk] at h
  exact IsMaximal.ne_top ‹_› h

end Ring

section CommRing

variable [CommRing R] [CommRing S]

/--
theorem `map_ne_bot_of_ne_bot` / 定理 `map_ne_bot_of_ne_bot`

English:
theorem map_ne_bot_of_ne_bot
  statement: {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  proof: (map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp.mt h

中文:
定理 map_ne_bot_of_ne_bot
  结论: {R S : 类型} [交换半环 R] [半环 S] [代数 R S]
  证明: (map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp.mt h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, map_eq_bot_iff_of_injective, mp.mt
-/
theorem map_ne_bot_of_ne_bot {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥) : map (algebraMap R S) I != ⊥ :=
  (map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp.mt h

/--
theorem `map_eq_iff_sup_ker_eq_of_surjective` / 定理 `map_eq_iff_sup_ker_eq_of_surjective`

English:
theorem map_eq_iff_sup_ker_eq_of_surjective
  statement: {I J : Ideal R} (f : R ->+* S)
  proof: by
  rw [← (comap_injective_of_surjective f hf).eq_iff]; rw [comap_map_of_surjective f hf]; rw [comap_map_of_surjective f hf]; rw [RingHom.ker_eq_comap_bot]

中文:
定理 map_eq_iff_sup_ker_eq_of_surjective
  结论: {I J : 理想 R} (f : R ->+* S)
  证明: by
  rw [← (comap_injective_of_surjective f hf).eq_iff]; rw [comap_map_of_surjective f hf]; rw [comap_map_of_surjective f hf]; rw [RingHom.ker_eq_comap_bot]

Depends on / 依赖: RingHom, RingHom.ker_eq_comap_bot, comap_injective_of_surjective, comap_map_of_surjective, eq_iff, ker_eq_comap_bot
-/
theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R ->+* S)
    (hf : Function.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker f := by
  rw [← (comap_injective_of_surjective f hf).eq_iff]; rw [comap_map_of_surjective f hf]; rw [comap_map_of_surjective f hf]; rw [RingHom.ker_eq_comap_bot]

/--
theorem `map_radical_of_surjective` / 定理 `map_radical_of_surjective`

English:
theorem map_radical_of_surjective
  statement: {f : R ->+* S} (hf : Function.Surjective f) {I : Ideal R}
  proof: by
  rw [radical_eq_sInf]; rw [radical_eq_sInf]
  have : forall J in {J : Ideal R | I <= J ∧ J.IsPrime}, RingHom.ker f <= J := fun J hJ => h.trans hJ.left
  convert! map_sInf hf this
  ext j
  constructor
  · rintro ⟨hj, hj'⟩
    have : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    have : J.IsPrime := hJ.right
    exact ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩

中文:
定理 map_radical_of_surjective
  结论: {f : R ->+* S} (hf : 函数.满射 f) {I : 理想 R}
  证明: by
  rw [radical_eq_sInf]; rw [radical_eq_sInf]
  have : forall J in {J : Ideal R | I <= J ∧ J.IsPrime}, RingHom.ker f <= J := fun J hJ => h.trans hJ.left
  convert! map_sInf hf this
  ext j
  constructor
  · rintro ⟨hj, hj'⟩
    have : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    have : J.IsPrime := hJ.right
    exact ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩

Depends on / 依赖: IsPrime, J.IsPrime, RingHom, RingHom.ker, Subtype, Subtype.val_injective, bot_unique, comap_isPrime, convert, h.trans, hJ.left, hJ.right, isOpen_discrete, j.IsPrime, le_trans, map_comap_of_surjective, map_isPrime_of_surjective, map_le_iff_le_comap, map_mono, map_sInf
-/
theorem map_radical_of_surjective {f : R ->+* S} (hf : Function.Surjective f) {I : Ideal R}
    (h : RingHom.ker f <= I) : map f I.radical = (map f I).radical := by
  rw [radical_eq_sInf]; rw [radical_eq_sInf]
  have : forall J in {J : Ideal R | I <= J ∧ J.IsPrime}, RingHom.ker f <= J := fun J hJ => h.trans hJ.left
  convert! map_sInf hf this
  ext j
  constructor
  · rintro ⟨hj, hj'⟩
    have : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    have : J.IsPrime := hJ.right
    exact ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩

end CommRing

end Ideal

namespace RingHom

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
variable (f : A ->+* B) (f_inv : B -> A)

/--
Definition of `liftOfRightInverseAux` / `liftOfRightInverseAux` 的定义

English:
definition liftOfRightInverseAux
  signature: (hf : Function.RightInverse f_inv f) (g : A ->+* C)
  body: { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_mul f]
      simp only [hf _] }

@[simp]

中文:
定义 liftOfRightInverseAux
  签名: (hf : 函数.右逆 f_inv f) (g : A ->+* C)
  定义体: { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_mul f]
      simp only [hf _] }

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.liftOfRightInverse, f.toAddMonoidHom, f_inv, g.toAddMonoidHom, liftOfRightInverse, map_mul, map_one, map_sub, mem_ker, sub_eq_zero, toAddMonoidHom
-/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A ->+* C)
    (hg : RingHom.ker f <= RingHom.ker g) :
    B ->+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g]; rw [← sub_eq_zero]; rw [← map_sub g]; rw [← mem_ker]
      apply hg
      rw [mem_ker]; rw [map_sub f]; rw [sub_eq_zero]; rw [map_mul f]
      simp only [hf _] }

@[simp]
/--
theorem `liftOfRightInverseAux_comp_apply` / 定理 `liftOfRightInverseAux_comp_apply`

English:
theorem liftOfRightInverseAux_comp_apply
  statement: (hf : Function.RightInverse f_inv f) (g : A ->+* C)
  proof: f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

中文:
定理 liftOfRightInverseAux_comp_apply
  结论: (hf : 函数.右逆 f_inv f) (g : A ->+* C)
  证明: f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

Depends on / 依赖: f.toAddMonoidHom.liftOfRightInverse_comp_apply, f_inv, g.toAddMonoidHom, liftOfRightInverse_comp_apply, toAddMonoidHom
-/
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A ->+* C)
    (hg : RingHom.ker f <= RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

/--
Definition of `liftOfRightInverse` / `liftOfRightInverse` 的定义

English:
definition liftOfRightInverse
  signature: (hf : Function.RightInverse f_inv f)
  body: f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

中文:
定义 liftOfRightInverse
  签名: (hf : 函数.右逆 f_inv f)
  定义体: f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

Depends on / 依赖: f.liftOfRightInverseAux, f_inv, liftOfRightInverseAux
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A ->+* C // RingHom.ker f <= RingHom.ker g } ≃ (B ->+* C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `RingHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
/--
Definition of `liftOfSurjective` / `liftOfSurjective` 的定义

English:
abbreviation liftOfSurjective
  signature: (hf : Function.Surjective f)
  body: f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

中文:
缩写 liftOfSurjective
  签名: (hf : 函数.满射 f)
  定义体: f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

Depends on / 依赖: Function, Function.rightInverse_surjInv, Function.surjInv, f.liftOfRightInverse, liftOfRightInverse, rightInverse_surjInv, surjInv
-/
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : A ->+* C // RingHom.ker f <= RingHom.ker g } ≃ (B ->+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

/--
theorem `liftOfRightInverse_comp_apply` / 定理 `liftOfRightInverse_comp_apply`

English:
theorem liftOfRightInverse_comp_apply
  statement: (hf : Function.RightInverse f_inv f)
  proof: f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

中文:
定理 liftOfRightInverse_comp_apply
  结论: (hf : 函数.右逆 f_inv f)
  证明: f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

Depends on / 依赖: f.liftOfRightInverseAux_comp_apply, f_inv, liftOfRightInverseAux_comp_apply
-/
theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

/--
theorem `liftOfRightInverse_comp` / 定理 `liftOfRightInverse_comp`

English:
theorem liftOfRightInverse_comp
  statement: (hf : Function.RightInverse f_inv f)
  proof: RingHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

中文:
定理 liftOfRightInverse_comp
  结论: (hf : 函数.右逆 f_inv f)
  证明: RingHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

Depends on / 依赖: RingHom, RingHom.ext, f.liftOfRightInverse_comp_apply, f_inv, liftOfRightInverse_comp_apply
-/
theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
RingHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

/--
theorem `eq_liftOfRightInverse` / 定理 `eq_liftOfRightInverse`

English:
theorem eq_liftOfRightInverse
  statement: (hf : Function.RightInverse f_inv f) (g : A ->+* C)
  proof: by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

中文:
定理 eq_liftOfRightInverse
  结论: (hf : 函数.右逆 f_inv f) (g : A ->+* C)
  证明: by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

Depends on / 依赖: apply_symm_apply, f.liftOfRightInverse, f_inv, liftOfRightInverse, simp_rw
-/
theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A ->+* C)
    (hg : RingHom.ker f <= RingHom.ker g) (h : B ->+* C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

/--
theorem `liftOfSurjective_comp_apply` / 定理 `liftOfSurjective_comp_apply`

English:
theorem liftOfSurjective_comp_apply
  statement: (hf : Function.Surjective f)
  proof: RingHom.liftOfRightInverse_comp_apply f _ _ g x

中文:
定理 liftOfSurjective_comp_apply
  结论: (hf : 函数.满射 f)
  证明: RingHom.liftOfRightInverse_comp_apply f _ _ g x

Depends on / 依赖: RingHom, RingHom.liftOfRightInverse_comp_apply, liftOfRightInverse_comp_apply
-/
theorem liftOfSurjective_comp_apply (hf : Function.Surjective f)
    (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) (x : A) :
    (f.liftOfSurjective hf) g (f x) = (g : A ->+* C) x :=
  RingHom.liftOfRightInverse_comp_apply f _ _ g x

/--
theorem `liftOfSurjective_comp` / 定理 `liftOfSurjective_comp`

English:
theorem liftOfSurjective_comp
  statement: (hf : Function.Surjective f)
  proof: RingHom.liftOfRightInverse_comp f _ _ g

中文:
定理 liftOfSurjective_comp
  结论: (hf : 函数.满射 f)
  证明: RingHom.liftOfRightInverse_comp f _ _ g

Depends on / 依赖: RingHom, RingHom.liftOfRightInverse_comp, liftOfRightInverse_comp
-/
theorem liftOfSurjective_comp (hf : Function.Surjective f)
    (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) :
    ((f.liftOfSurjective hf) g).comp f = (g : A ->+* C) :=
  RingHom.liftOfRightInverse_comp f _ _ g

/--
theorem `eq_liftOfSurjective` / 定理 `eq_liftOfSurjective`

English:
theorem eq_liftOfSurjective
  statement: (hf : Function.Surjective f) (g : A ->+* C)
  proof: RingHom.eq_liftOfRightInverse f _ _ g _ _ hh

中文:
定理 eq_liftOfSurjective
  结论: (hf : 函数.满射 f) (g : A ->+* C)
  证明: RingHom.eq_liftOfRightInverse f _ _ g _ _ hh

Depends on / 依赖: RingHom, RingHom.eq_liftOfRightInverse, eq_liftOfRightInverse
-/
theorem eq_liftOfSurjective (hf : Function.Surjective f) (g : A ->+* C)
    (hg : RingHom.ker f <= RingHom.ker g) (h : B ->+* C) (hh : h.comp f = g) :
    h = f.liftOfSurjective hf ⟨g, hg⟩ :=
  RingHom.eq_liftOfRightInverse f _ _ g _ _ hh

end RingHom

set_option backward.isDefEq.respectTransparency false in
/-- Any ring isomorphism induces an order isomorphism of ideals. -/
@[simps apply]
/--
Definition of `RingEquiv.idealComapOrderIso` / `RingEquiv.idealComapOrderIso` 的定义

English:
definition RingEquiv.idealComapOrderIso
  signature: {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S)
  body: I.comap e
  invFun I := I.map e
  left_inv I := I.map_comap_of_surjective _ e.surjective
  right_inv I := I.comap_map_of_bijective _ e.bijective
  map_rel_iff' := by
    simp [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ e.surjective]

@[simp]

中文:
定义 环等价.idealComapOrderIso
  签名: {R S : 类型} [半环 R] [半环 S] (e : R ≃+* S)
  定义体: I.comap e
  invFun I := I.map e
  left_inv I := I.map_comap_of_surjective _ e.surjective
  right_inv I := I.comap_map_of_bijective _ e.bijective
  map_rel_iff' := by
    simp [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ e.surjective]

@[simp]

Depends on / 依赖: I.comap
-/
def RingEquiv.idealComapOrderIso {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Ideal S ≃o Ideal R where
  toFun I := I.comap e
  invFun I := I.map e
  left_inv I := I.map_comap_of_surjective _ e.surjective
  right_inv I := I.comap_map_of_bijective _ e.bijective
  map_rel_iff' := by
    simp [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ e.surjective]

@[simp]
/--
lemma `RingEquiv.idealComapOrderIso_symm_apply` / 引理 `RingEquiv.idealComapOrderIso_symm_apply`

English:
lemma RingEquiv.idealComapOrderIso_symm_apply
  proof: rfl

中文:
引理 环等价.idealComapOrderIso_symm_apply
  证明: rfl
-/
lemma RingEquiv.idealComapOrderIso_symm_apply
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (I : Ideal R) :
    e.idealComapOrderIso.symm I = I.map e :=
  rfl

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ->ₐ[R] B)

/--
lemma `ker_coe` / 引理 `ker_coe`

English:
lemma ker_coe
  statement: RingHom.ker f = RingHom.ker (f : A ->+* B)
  proof: rfl

中文:
引理 ker_coe
  结论: 环态射.ker f = 环态射.ker (f : A ->+* B)
  证明: rfl
-/
lemma ker_coe : RingHom.ker f = RingHom.ker (f : A ->+* B) := rfl

/--
lemma `coe_ideal_map` / 引理 `coe_ideal_map`

English:
lemma coe_ideal_map
  given: (I : Ideal A)
  proof: rfl

中文:
引理 coe_ideal_map
  条件: (I : 理想 A)
  证明: rfl
-/
lemma coe_ideal_map (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A ->+* B) I := rfl

/--
lemma `comap_ker` / 引理 `comap_ker`

English:
lemma comap_ker
  given: {C : Type*} [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B)
  proof: RingHom.comap_ker f.toRingHom g.toRingHom

中文:
引理 comap_ker
  条件: {C : 类型} [半环 C] [代数 R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B)
  证明: RingHom.comap_ker f.toRingHom g.toRingHom

Depends on / 依赖: RingHom, RingHom.comap_ker, comap_ker, f.toRingHom, g.toRingHom, toRingHom
-/
lemma comap_ker {C : Type*} [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B) :
    (RingHom.ker f).comap g = RingHom.ker (f.comp g) :=
  RingHom.comap_ker f.toRingHom g.toRingHom

end AlgHom

namespace Algebra

variable {R : Type*} [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]

/-- The induced linear map from `I` to the span of `I` in an `R`-algebra `S`. -/
@[simps!]
/--
Definition of `idealMap` / `idealMap` 的定义

English:
definition idealMap
  signature: (I : Ideal R)
  body: (Algebra.linearMap R S).restrict (q := (I.map (algebraMap R S)).restrictScalars R)
    (fun _ => Ideal.mem_map_of_mem _)

@[simp]

中文:
定义 idealMap
  签名: (I : 理想 R)
  定义体: (Algebra.linearMap R S).restrict (q := (I.map (algebraMap R S)).restrictScalars R)
    (fun _ => Ideal.mem_map_of_mem _)

@[simp]

Depends on / 依赖: Algebra, Algebra.linearMap, I.map, Ideal.mem_map_of_mem, algebraMap, linearMap, mem_map_of_mem, restrict, restrictScalars
-/
def idealMap (I : Ideal R) : I ->ₗ[R] I.map (algebraMap R S) :=
  (Algebra.linearMap R S).restrict (q := (I.map (algebraMap R S)).restrictScalars R)
    (fun _ => Ideal.mem_map_of_mem _)

@[simp]
/--
lemma `idealMap_mul` / 引理 `idealMap_mul`

English:
lemma idealMap_mul
  given: (I : Ideal R) (x y : I)
  proof: by
  ext
  simp

中文:
引理 idealMap_mul
  条件: (I : 理想 R) (x y : I)
  证明: by
  ext
  simp
-/
lemma idealMap_mul (I : Ideal R) (x y : I) :
    idealMap S I (x * y) = idealMap S I x * idealMap S I y := by
  ext
  simp

end Algebra

@[simp]
/--
theorem `FaithfulSMul.ker_algebraMap_eq_bot` / 定理 `FaithfulSMul.ker_algebraMap_eq_bot`

English:
theorem FaithfulSMul.ker_algebraMap_eq_bot
  statement: (R A : Type*) [CommSemiring R] [Semiring A]
  proof: by
  ext; simp

中文:
定理 忠实标量乘法.ker_algebraMap_eq_bot
  结论: (R A : 类型) [交换半环 R] [半环 A]
  证明: by
  ext; simp
-/
theorem FaithfulSMul.ker_algebraMap_eq_bot (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] : RingHom.ker (algebraMap R A) = ⊥ := by
  ext; simp

section PrincipalIdeal

instance {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S) (I : Ideal R) [I.IsPrincipal] :
    (I.map f).IsPrincipal := by
  obtain ⟨x, rfl⟩ := Submodule.IsPrincipal.principal I
  exact ⟨f x, by
    rw [← Ideal.span]; rw [← Set.image_singleton]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [Ideal.submodule_span_eq]⟩

end PrincipalIdeal

/--
lemma `RingHom.ker_evalRingHom` / 引理 `RingHom.ker_evalRingHom`

English:
lemma RingHom.ker_evalRingHom
  statement: {ι : Type*} [DecidableEq ι] (R : ι -> Type*)
  proof: by
  refine le_antisymm (fun x hx => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
  rw [Ideal.mem_span_singleton]
  use x + Pi.single i 1
  simp [mul_add, sub_mul, one_mul, ← Pi.single_mul_left, hx]

中文:
引理 环态射.ker_evalRingHom
  结论: {ι : 类型} [DecidableEq ι] (R : ι -> 类型)
  证明: by
  refine le_antisymm (fun x hx => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
  rw [Ideal.mem_span_singleton]
  use x + Pi.single i 1
  simp [mul_add, sub_mul, one_mul, ← Pi.single_mul_left, hx]

Depends on / 依赖: Ideal.mem_span_singleton, Ideal.span_le, Pi.evalRingHom_apply, Pi.single, Pi.single_mul_left, RingHom, RingHom.mem_ker, evalRingHom_apply, le_antisymm, mem_ker, mem_span_singleton, mul_add, one_mul, single, single_mul_left, span_le, sub_mul
-/
lemma RingHom.ker_evalRingHom {ι : Type*} [DecidableEq ι] (R : ι -> Type*)
    [forall i, CommRing (R i)] (i : ι) :
    RingHom.ker (Pi.evalRingHom R i) = Ideal.span {1 - Pi.single i 1} := by
  refine le_antisymm (fun x hx => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
  rw [Ideal.mem_span_singleton]
  use x + Pi.single i 1
  simp [mul_add, sub_mul, one_mul, ← Pi.single_mul_left, hx]

/--
lemma `Ideal.exists_of_comap_eq_ker_sup` / 引理 `Ideal.exists_of_comap_eq_ker_sup`

English:
lemma Ideal.exists_of_comap_eq_ker_sup
  statement: {A B : Type*} [Ring A] [Ring B] (f : A ->+* B)
  proof: by
  rcases surj x with ⟨x', hx'⟩
  rw [← hx']; rw [← Ideal.mem_comap]; rw [eq] at hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
  use z, hz
  simpa [← hx', ← hyz, ← RingHom.mem_ker] using hy

中文:
引理 理想.存在_of_comap_eq_ker_sup
  结论: {A B : 类型} [环 A] [环 B] (f : A ->+* B)
  证明: by
  rcases surj x with ⟨x', hx'⟩
  rw [← hx']; rw [← Ideal.mem_comap]; rw [eq] at hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
  use z, hz
  simpa [← hx', ← hyz, ← RingHom.mem_ker] using hy

Depends on / 依赖: Ideal.mem_comap, RingHom, RingHom.mem_ker, Submodule, Submodule.mem_sup.mp, mem_comap, mem_ker, mem_sup
-/
lemma Ideal.exists_of_comap_eq_ker_sup {A B : Type*} [Ring A] [Ring B] (f : A ->+* B)
    (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A}
    (eq : I.comap f = RingHom.ker f ⊔ J) {x : B} (hx : x in I) : exists y in J, f y = x := by
  rcases surj x with ⟨x', hx'⟩
  rw [← hx']; rw [← Ideal.mem_comap]; rw [eq] at hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
  use z, hz
  simpa [← hx', ← hyz, ← RingHom.mem_ker] using hy

/--
lemma `Ideal.eq_map_of_comap_eq_ker_sup` / 引理 `Ideal.eq_map_of_comap_eq_ker_sup`

English:
lemma Ideal.eq_map_of_comap_eq_ker_sup
  statement: {A B : Type*} [CommRing A] [CommRing B] (f : A ->+* B)
  proof: by
  refine le_antisymm (fun x hx => ?_)
    (Ideal.map_le_iff_le_comap.mpr (le_of_le_of_eq le_sup_right eq.symm))
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq hx with ⟨y, mem, hy⟩
  simpa [← hy] using Ideal.mem_map_of_mem _ mem

中文:
引理 理想.eq_map_of_comap_eq_ker_sup
  结论: {A B : 类型} [交换环 A] [交换环 B] (f : A ->+* B)
  证明: by
  refine le_antisymm (fun x hx => ?_)
    (Ideal.map_le_iff_le_comap.mpr (le_of_le_of_eq le_sup_right eq.symm))
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq hx with ⟨y, mem, hy⟩
  simpa [← hy] using Ideal.mem_map_of_mem _ mem

Depends on / 依赖: Ideal.exists_of_comap_eq_ker_sup, Ideal.map_le_iff_le_comap.mpr, Ideal.mem_map_of_mem, eq.symm, exists_of_comap_eq_ker_sup, le_antisymm, le_of_le_of_eq, le_sup_right, map_le_iff_le_comap, mem_map_of_mem
-/
lemma Ideal.eq_map_of_comap_eq_ker_sup {A B : Type*} [CommRing A] [CommRing B] (f : A ->+* B)
    (surj : Function.Surjective f) {I : Ideal B} {J : Ideal A}
    (eq : I.comap f = RingHom.ker f ⊔ J) : I = J.map f := by
  refine le_antisymm (fun x hx => ?_)
    (Ideal.map_le_iff_le_comap.mpr (le_of_le_of_eq le_sup_right eq.symm))
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq hx with ⟨y, mem, hy⟩
  simpa [← hy] using Ideal.mem_map_of_mem _ mem
