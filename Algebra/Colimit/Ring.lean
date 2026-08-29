/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Finset.Order
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of rings, and fields

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable rings or fields.

It is constructed as a quotient of the free commutative ring instead of a quotient of
the disjoint union so as to make the operations (addition etc.) "computable".

## Main definition

* `Ring.DirectLimit G f`

-/

@[expose] public section

assert_not_exists Cardinal

suppress_compilation
noncomputable section -- needed for `deriving`

variable {ι : Type*} [Preorder ι] (G : ι -> Type*)

open Submodule

namespace Ring

variable [forall i, CommRing (G i)]

section

variable (f : forall i j, i <= j -> G i -> G j)

open FreeCommRing

/--
Definition of `DirectLimit` / `DirectLimit` 的定义

English:
definition DirectLimit
  signature: : Type _
  body: FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (exists i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (exists i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (exists i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              exists i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

中文:
定义 DirectLimit
  签名: : 类型 _
  定义体: FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (exists i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (exists i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (exists i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              exists i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

Depends on / 依赖: FreeCommRing, Ideal.span
-/
def DirectLimit : Type _ :=
  FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (exists i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (exists i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (exists i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              exists i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

namespace DirectLimit

/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i ->+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x => Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σ i, G i))
map_one' := Ideal.Quotient.eq.2 subset_span Or.inr Or.inl ⟨i, rfl⟩
      map_mul' := fun x y =>
Ideal.Quotient.eq.2 subset_span Or.inr Or.inr Or.inr ⟨i, x, y, rfl⟩ }
fun x y => Ideal.Quotient.eq.2 subset_span Or.inr Or.inr Or.inl ⟨i, x, y, rfl⟩

variable {G f}

/--
theorem `quotientMk_of` / 定理 `quotientMk_of`

English:
theorem quotientMk_of
  given: (i x)
  statement: Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x
  proof: rfl

中文:
定理 quotientMk_of
  条件: (i x)
  结论: 理想.商.mk _ (.of ⟨i, x⟩) = of G f i x
  证明: rfl
-/
theorem quotientMk_of (i x) : Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x :=
  rfl

/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: Ideal.Quotient.eq.2 subset_span Or.inl ⟨i, j, hij, x, rfl⟩

中文:
定理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: Ideal.Quotient.eq.2 subset_span Or.inl ⟨i, j, hij, x, rfl⟩
-/
@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
Ideal.Quotient.eq.2 subset_span Or.inl ⟨i, j, hij, x, rfl⟩

/--
theorem `exists_of` / 定理 `exists_of`

English:
theorem exists_of
  given: [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f)
  proof: by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ => ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

中文:
定理 存在_of
  条件: [非空 ι] [IsDirectedOrder ι] (z : DirectLimit G f)
  证明: by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ => ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

Depends on / 依赖: Classical, Classical.arbitrary, Ideal.Quotient.mk_surjective, Quotient, arbitrary, exists_ge_ge, induction_on, map_add, map_mul, mk_surjective, of_f, z.induction_on
-/
theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) :
    exists i x, of G f i x = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ => ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

section

open Polynomial

variable {f' : forall i j, i <= j -> G i ->+* G j}

nonrec theorem Polynomial.exists_of [Nonempty ι] [IsDirectedOrder ι]
    (q : Polynomial (DirectLimit G fun i j h => f' i j h)) :
    exists i p, Polynomial.map (of G (fun i j h => f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z =>
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ =>
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2), by
        rw [Polynomial.map_add]; rw [map_map]; rw [map_map]; rw [← ih₁]; rw [← ih₂]
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, of_f]⟩)
    fun n z _ =>
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩

end

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
  proof: let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

中文:
定理 induction_on
  结论: [非空 ι] [IsDirectedOrder ι] {C : DirectLimit G f -> 命题}
  证明: let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

Depends on / 依赖: exists_of
-/
theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop}
    (z : DirectLimit G f) (ih : forall i x, C (of G f i x)) : C z :=
  let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

variable (P : Type*) [CommRing P]

open FreeCommRing

variable (G f) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σ i, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ <=
          Ideal.comap (FreeCommRing.lift fun x : Σ i : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe]; rw [Ideal.mem_comap]; rw [mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [map_sub, lift_of, Hg, map_one, map_add, map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

中文:
定义 lift
  签名: (g : 对任意 i, G i ->+* P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σ i, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ <=
          Ideal.comap (FreeCommRing.lift fun x : Σ i : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe]; rw [Ideal.mem_comap]; rw [mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [map_sub, lift_of, Hg, map_one, map_add, map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

Depends on / 依赖: FreeCommRing, FreeCommRing.lift, Ideal.Quotient.lift, Ideal.comap, Ideal.mem_comap, Ideal.span, Ideal.span_le, Quotient, SetLike, SetLike.mem_coe, lift_of, map_add, map_mul, map_one, map_sub, mem_bot, mem_coe, mem_comap, span_le, sub_s
-/
def lift (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σ i, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ <=
          Ideal.comap (FreeCommRing.lift fun x : Σ i : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe]; rw [Ideal.mem_comap]; rw [mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [map_sub, lift_of, Hg, map_one, map_add, map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

variable (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: FreeCommRing.lift_of _ _

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: FreeCommRing.lift_of _ _

@[ext]
-/
@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i))
  proof: Ideal.Quotient.ringHom_ext FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

@[simp]

中文:
定理 hom_ext
  条件: {g₁ g₂ : DirectLimit G f ->+* P} (h : 对任意 i, g₁.comp (of G f i) = g₂.comp (of G f i))
  证明: Ideal.Quotient.ringHom_ext FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

@[simp]

Depends on / 依赖: FreeCommRing, FreeCommRing.hom_ext, Ideal.Quotient.ringHom_ext, Quotient, hom_ext, ringHom_ext
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
Ideal.Quotient.ringHom_ext FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (F : DirectLimit G f ->+* P)
  proof: by
  ext; simp

@[simp]

中文:
定理 lift_comp_of
  条件: (F : DirectLimit G f ->+* P)
  证明: by
  ext; simp

@[simp]
-/
theorem lift_comp_of (F : DirectLimit G f ->+* P) :
    lift G f _ (fun i => F.comp <| of G f i) (fun i j hij x => by simp) = F := by
  ext; simp

@[simp]
/--
theorem `lift_of'` / 定理 `lift_of'`

English:
theorem lift_of'
  statement: lift G f _ (of G f) (fun i j hij x => by simp) = .id _
  proof: by
  ext; simp

中文:
定理 lift_of'
  结论: lift G f _ (of G f) (fun i j hij x => by simp) = .id _
  证明: by
  ext; simp
-/
theorem lift_of' : lift G f _ (of G f) (fun i j hij x => by simp) = .id _ := by
  ext; simp

/--
lemma `lift_injective` / 引理 `lift_injective`

English:
lemma lift_injective
  statement: [Nonempty ι] [IsDirectedOrder ι]
  proof: by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

中文:
引理 lift_injective
  结论: [非空 ι] [IsDirectedOrder ι]
  证明: by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

Depends on / 依赖: DirectLimit, DirectLimit.induction_on, ExpChar, Nat.not_prime_one, Prod.charP, induction_on, injective, injective_iff_map_eq_zero, lift_of, map_zero, not_prime_one, simp_rw
-/
lemma lift_injective [Nonempty ι] [IsDirectedOrder ι]
    (injective : forall i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) := by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

section OfZeroExact

variable (f' : forall i j, i <= j -> G i ->+* G j)
variable [DirectedSystem G fun i j h => f' i j h] [IsDirectedOrder ι]
variable (G f)

open _root_.DirectLimit in
/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: [Nonempty ι]
  body: .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]

中文:
定义 ringEquiv
  签名: [非空 ι]
  定义体: .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]

Depends on / 依赖: CharP.cast_eq_iff_mod_eq, Lean.Grind.Semiring.ofNat_eq_natCast, Ring.lift, Ring.of, Semiring, cast_eq_iff_mod_eq, eq_of_le, ofNat_eq_natCast, ofRingHom, of_f
-/
def ringEquiv [Nonempty ι] : DirectLimit G (f' · · ·) ≃+* _root_.DirectLimit G f' :=
  .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ => .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ => of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]
/--
theorem `ringEquiv_of` / 定理 `ringEquiv_of`

English:
theorem ringEquiv_of
  given: [Nonempty ι] {i g}
  statement: ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧
  proof: by
  simp [ringEquiv]

@[simp]

中文:
定理 ringEquiv_of
  条件: [非空 ι] {i g}
  结论: ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧
  证明: by
  simp [ringEquiv]

@[simp]

Depends on / 依赖: ringEquiv
-/
theorem ringEquiv_of [Nonempty ι] {i g} : ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧ := by
  simp [ringEquiv]

@[simp]
/--
theorem `ringEquiv_symm_mk` / 定理 `ringEquiv_symm_mk`

English:
theorem ringEquiv_symm_mk
  given: [Nonempty ι] {g}
  statement: (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2
  proof: rfl

中文:
定理 ringEquiv_symm_mk
  条件: [非空 ι] {g}
  结论: (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2
  证明: rfl
-/
theorem ringEquiv_symm_mk [Nonempty ι] {g} : (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2 := rfl

variable {G f'}
/--
theorem `of.zero_exact` / 定理 `of.zero_exact`

English:
theorem of.zero_exact
  given: {i x} (hix : of G (f' · · ·) i x = 0)
  proof: by
  have := Nonempty.intro i
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix

中文:
定理 of.zero_exact
  条件: {i x} (hix : of G (f' · · ·) i x = 0)
  证明: by
  have := Nonempty.intro i
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix
-/
theorem of.zero_exact {i x} (hix : of G (f' · · ·) i x = 0) :
    exists (j : _) (hij : i <= j), f' i j hij x = 0 := by
  have := Nonempty.intro i
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix

end OfZeroExact

variable (f' : forall i j, i <= j -> G i ->+* G j)

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: [IsDirectedOrder ι] [DirectedSystem G fun i j h => f' i j h]
  proof: have := Nonempty.intro i
  ((ringEquiv _ _).comp_injective _).mp
    fun _ _ eq => DirectLimit.mk_injective f' hf _ (by simpa only [← ringEquiv_of])

中文:
定理 of_injective
  结论: [IsDirectedOrder ι] [DirectedSystem G fun i j h => f' i j h]
  证明: have := Nonempty.intro i
  ((ringEquiv _ _).comp_injective _).mp
    fun _ _ eq => DirectLimit.mk_injective f' hf _ (by simpa only [← ringEquiv_of])

Depends on / 依赖: DirectLimit, DirectLimit.mk_injective, Nonempty, Nonempty.intro, comp_injective, mk_injective, ringEquiv, ringEquiv_of
-/
theorem of_injective [IsDirectedOrder ι] [DirectedSystem G fun i j h => f' i j h]
    (hf : forall i j hij, Function.Injective (f' i j hij)) (i) :
    Function.Injective (of G (fun i j h => f' i j h) i) :=
  have := Nonempty.intro i
  ((ringEquiv _ _).comp_injective _).mp
    fun _ _ eq => DirectLimit.mk_injective f' hf _ (by simpa only [← ringEquiv_of])

section functorial

variable {f : forall i j, i <= j -> G i ->+* G j}
variable {G' : ι -> Type*} [forall i, CommRing (G' i)]
variable {f' : forall i j, i <= j -> G' i ->+* G' j}
variable {G'' : ι -> Type*} [forall i, CommRing (G'' i)]
variable {f'' : forall i j, i <= j -> G'' i ->+* G'' j}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : (i : ι) -> G i ->+* G' i)
  body: lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1]; rw [of_f]

中文:
定义 map
  签名: (g : (i : ι) -> G i ->+* G' i)
  定义体: lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1]; rw [of_f]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, comp_apply, congr_fun, of_f
-/
def map (g : (i : ι) -> G i ->+* G' i)
    (hg : forall i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G (fun _ _ h => f _ _ h) ->+* DirectLimit G' fun _ _ h => f' _ _ h :=
  lift _ _ _ (fun i => (of _ _ _).comp (g i)) fun i j h g => by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1]; rw [of_f]

/--
lemma `map_apply_of` / 引理 `map_apply_of`

English:
lemma map_apply_of
  statement: (g : (i : ι) -> G i ->+* G' i)
  proof: lift_of _ _ _ _ _

中文:
引理 map_apply_of
  结论: (g : (i : ι) -> G i ->+* G' i)
  证明: lift_of _ _ _ _ _
-/
@[simp] lemma map_apply_of (g : (i : ι) -> G i ->+* G' i)
    (hg : forall i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G _ _ x) = of G' (fun _ _ h => f' _ _ h) i (g i x) :=
  lift_of _ _ _ _ _

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  proof: by
  ext; simp

中文:
引理 map_id
  证明: by
  ext; simp
-/
@[simp] lemma map_id :
    map (fun _ => RingHom.id _) (fun _ _ _ => rfl) = .id (DirectLimit G fun _ _ h => f _ _ h) := by
  ext; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: (g₁ : (i : ι) -> G i ->+* G' i) (g₂ : (i : ι) -> G' i ->+* G'' i)
  proof: by
  ext; simp

中文:
引理 map_comp
  结论: (g₁ : (i : ι) -> G i ->+* G' i) (g₂ : (i : ι) -> G' i ->+* G'' i)
  证明: by
  ext; simp
-/
lemma map_comp (g₁ : (i : ι) -> G i ->+* G' i) (g₂ : (i : ι) -> G' i ->+* G'' i)
    (hg₁ : forall i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : forall i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G (fun _ _ h => f _ _ h) ->+* DirectLimit G'' fun _ _ h => f'' _ _ h) =
    (map (fun i => (g₂ i).comp (g₁ i)) fun i j h => by
      rw [RingHom.comp_assoc]; rw [hg₁ i]; rw [← RingHom.comp_assoc]; rw [hg₂ i]; rw [RingHom.comp_assoc] :
      DirectLimit G (fun _ _ h => f _ _ h) ->+* DirectLimit G'' fun _ _ h => f'' _ _ h) := by
  ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : (i : ι) -> G i ≃+* G' i)
  body: RingEquiv.ofRingHom
    (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

中文:
定义 congr
  签名: (e : (i : ι) -> G i ≃+* G' i)
  定义体: RingEquiv.ofRingHom
    (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, Function, Function.comp_apply, RingEquiv, RingEquiv.apply_symm_apply, RingEquiv.ofRingHom, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_coe, RingHom.coe_comp, apply_symm_apply, coe_coe, coe_comp, comp_apply, congr_fun, map_comp, ofRingHom, toRingHom_eq_coe
-/
def congr (e : (i : ι) -> G i ≃+* G' i)
    (he : forall i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G (fun _ _ h => f _ _ h) ≃+* DirectLimit G' fun _ _ h => f' _ _ h :=
  RingEquiv.ofRingHom
    (map (e ·) he)
    (map (fun i => (e i).symm) fun i j h => DFunLike.ext _ _ fun x => by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

/--
lemma `congr_apply_of` / 引理 `congr_apply_of`

English:
lemma congr_apply_of
  statement: (e : (i : ι) -> G i ≃+* G' i)
  proof: map_apply_of _ he _

中文:
引理 congr_apply_of
  结论: (e : (i : ι) -> G i ≃+* G' i)
  证明: map_apply_of _ he _

Depends on / 依赖: map_apply_of
-/
lemma congr_apply_of (e : (i : ι) -> G i ≃+* G' i)
    (he : forall i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G _ i g) = of G' (fun _ _ h => f' _ _ h) i (e i g) :=
  map_apply_of _ he _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `congr_symm_apply_of` / 引理 `congr_symm_apply_of`

English:
lemma congr_symm_apply_of
  statement: (e : (i : ι) -> G i ≃+* G' i)
  proof: by
  simp only [congr, RingEquiv.ofRingHom_symm_apply, map_apply_of, RingHom.coe_coe]

中文:
引理 congr_symm_apply_of
  结论: (e : (i : ι) -> G i ≃+* G' i)
  证明: by
  simp only [congr, RingEquiv.ofRingHom_symm_apply, map_apply_of, RingHom.coe_coe]

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom_symm_apply, RingHom, RingHom.coe_coe, coe_coe, map_apply_of, ofRingHom_symm_apply
-/
lemma congr_symm_apply_of (e : (i : ι) -> G i ≃+* G' i)
    (he : forall i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' _ i g) = of G (fun _ _ h => f _ _ h) i ((e i).symm g) := by
  simp only [congr, RingEquiv.ofRingHom_symm_apply, map_apply_of, RingHom.coe_coe]

end functorial

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirectedOrder ι] [forall i, Field (G i)]
variable (f : forall i j, i <= j -> G i -> G j)
variable (f' : forall i j, i <= j -> G i ->+* G j)

namespace DirectLimit

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [DirectedSystem G (f' · · ·)]
  body: ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
        change (0 : Ring.DirectLimit G (f' · · ·)) != 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩

中文:
实例 nontrivial
  签名: [DirectedSystem G (f' · · ·)]
  定义体: ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
        change (0 : Ring.DirectLimit G (f' · · ·)) != 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩

Depends on / 依赖: DirectLimit, H.symm, Nonempty, Nonempty.elim, Ring.DirectLimit, Ring.DirectLimit.of, Ring.DirectLimit.of.zero_exact, infer_instance, map_one, one_ne_zero, zero_exact
-/
instance nontrivial [DirectedSystem G (f' · · ·)] :
    Nontrivial (Ring.DirectLimit G (f' · · ·)) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
        change (0 : Ring.DirectLimit G (f' · · ·)) != 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩

/--
theorem `exists_inv` / 定理 `exists_inv`

English:
theorem exists_inv
  given: {p : Ring.DirectLimit G f}
  statement: p != 0 -> exists y, p * y = 1
  proof: Ring.DirectLimit.induction_on p fun i x H =>
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul]; rw [mul_inv_cancel₀ fun h : x = 0 => H by rw [h]; rw [(Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

中文:
定理 存在_inv
  条件: {p : 环.DirectLimit G f}
  结论: p != 0 -> 存在 y, p * y = 1
  证明: Ring.DirectLimit.induction_on p fun i x H =>
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul]; rw [mul_inv_cancel₀ fun h : x = 0 => H by rw [h]; rw [(Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

Depends on / 依赖: DirectLimit, Ring.DirectLimit.induction_on, Ring.DirectLimit.of, induction_on, map_mul, map_one, map_zero
-/
theorem exists_inv {p : Ring.DirectLimit G f} : p != 0 -> exists y, p * y = 1 :=
  Ring.DirectLimit.induction_on p fun i x H =>
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul]; rw [mul_inv_cancel₀ fun h : x = 0 => H by rw [h]; rw [(Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

section


open scoped Classical in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (p : Ring.DirectLimit G f)
  body: if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)

中文:
定义 inv
  签名: (p : 环.DirectLimit G f)
  定义体: if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)

Depends on / 依赖: Classical, Classical.choose, DirectLimit, DirectLimit.exists_inv, exists_inv
-/
noncomputable def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: {p : Ring.DirectLimit G f} (hp : p != 0)
  statement: p * inv G f p = 1
  proof: by
  rw [inv]; rw [dif_neg hp]; rw [Classical.choose_spec (DirectLimit.exists_inv G f hp)]

中文:
定理 mul_inv_cancel
  条件: {p : 环.DirectLimit G f} (hp : p != 0)
  结论: p * inv G f p = 1
  证明: by
  rw [inv]; rw [dif_neg hp]; rw [Classical.choose_spec (DirectLimit.exists_inv G f hp)]
-/
protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p != 0) : p * inv G f p = 1 := by
  rw [inv]; rw [dif_neg hp]; rw [Classical.choose_spec (DirectLimit.exists_inv G f hp)]

/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: {p : Ring.DirectLimit G f} (hp : p != 0)
  statement: inv G f p * p = 1
  proof: by
  rw [_root_.mul_comm]; rw [DirectLimit.mul_inv_cancel G f hp]

中文:
定理 inv_mul_cancel
  条件: {p : 环.DirectLimit G f} (hp : p != 0)
  结论: inv G f p * p = 1
  证明: by
  rw [_root_.mul_comm]; rw [DirectLimit.mul_inv_cancel G f hp]
-/
protected theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p != 0) : inv G f p * p = 1 := by
  rw [_root_.mul_comm]; rw [DirectLimit.mul_inv_cancel G f hp]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev field [DirectedSystem G (f' · · ·)]
  body: inv G (f' · · ·)
  mul_inv_cancel := fun _ => DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

中文:
缩写 noncomputable
  签名: abbrev field [DirectedSystem G (f' · · ·)]
  定义体: inv G (f' · · ·)
  mul_inv_cancel := fun _ => DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl
-/
protected noncomputable abbrev field [DirectedSystem G (f' · · ·)] :
    Field (Ring.DirectLimit G (f' · · ·)) where
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  inv := inv G (f' · · ·)
  mul_inv_cancel := fun _ => DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

end

end DirectLimit

end Field
