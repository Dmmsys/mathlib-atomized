/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.ProxyType

/-!
# Finiteness instances on multi-spans
-/

public section

namespace CategoryTheory.Limits

namespace WalkingMulticospan

variable {J : MulticospanShape} [Fintype J.L] [Fintype J.R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (WalkingMulticospan J)
  body: .ofEquiv _ (proxy_equiv% (WalkingMulticospan J))

中文:
实例 :
  签名: Fintype (WalkingMulticospan J)
  定义体: .ofEquiv _ (proxy_equiv% (WalkingMulticospan J))

Depends on / 依赖: WalkingMulticospan, ofEquiv, proxy_equiv
-/
instance : Fintype (WalkingMulticospan J) := .ofEquiv _ (proxy_equiv% (WalkingMulticospan J))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: J.L] [DecidableEq J.R] : FinCategory (WalkingMulticospan J) where

中文:
实例 [DecidableEq
  签名: J.L] [DecidableEq J.R] : FinCategory (WalkingMulticospan J) where
-/
instance [DecidableEq J.L] [DecidableEq J.R] : FinCategory (WalkingMulticospan J) where
  fintypeHom
    | .left a, .left b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩
    | .left a, .right b => ⟨⟨(if e : J.fst b = a then {eqToHom (e ▸ rfl) ≫ Hom.fst b} else 0) +
        (if e : J.snd b = a then {eqToHom (e ▸ rfl) ≫ Hom.snd b} else 0), by
        split_ifs with h₁ h₂
        · simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
            Multiset.nodup_singleton, and_true]
          let f : ((left a : WalkingMulticospan J) ⟶ right b) -> Prop
            | .fst a => True
            | .snd a => False
          apply ne_of_apply_ne f
          conv_lhs => tactic => subst h₁; simp only [eqToHom_refl, Category.id_comp, f]
          conv_rhs => tactic => subst h₂; simp only [eqToHom_refl, Category.id_comp, f]
          simp
        all_goals simp⟩, by rintro ⟨⟩ <;> simp⟩
    | .right a, .left b => ⟨∅, by rintro ⟨⟩⟩
    | .right a, .right b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩

end WalkingMulticospan

namespace WalkingMultispan

variable {J : MultispanShape} [Fintype J.L] [Fintype J.R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (WalkingMultispan J)
  body: .ofEquiv _ (proxy_equiv% (WalkingMultispan J))

中文:
实例 :
  签名: Fintype (WalkingMultispan J)
  定义体: .ofEquiv _ (proxy_equiv% (WalkingMultispan J))

Depends on / 依赖: WalkingMultispan, ofEquiv, proxy_equiv
-/
instance : Fintype (WalkingMultispan J) := .ofEquiv _ (proxy_equiv% (WalkingMultispan J))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: J.L] [DecidableEq J.R] : FinCategory (WalkingMultispan J) where

中文:
实例 [DecidableEq
  签名: J.L] [DecidableEq J.R] : FinCategory (WalkingMultispan J) where
-/
instance [DecidableEq J.L] [DecidableEq J.R] : FinCategory (WalkingMultispan J) where
  fintypeHom
    | .left a, .left b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩
    | .left a, .right b => ⟨⟨(if e : J.fst a = b then {Hom.fst a ≫ eqToHom (e ▸ rfl)} else 0) +
        (if e : J.snd a = b then {Hom.snd a ≫ eqToHom (e ▸ rfl)} else 0), by
        split_ifs with h₁ h₂
        · simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
            Multiset.nodup_singleton, and_true]
          let f : ((left a : WalkingMultispan J) ⟶ right b) -> Prop
            | .fst a => True
            | .snd a => False
          apply ne_of_apply_ne f
          conv_lhs => tactic => subst h₁; simp only [eqToHom_refl, f]
          conv_rhs => tactic => subst h₂; simp only [eqToHom_refl, f]
          simp
        all_goals simp⟩, by rintro ⟨⟩ <;> simp⟩
    | .right a, .left b => ⟨∅, by rintro ⟨⟩⟩
    | .right a, .right b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩

end WalkingMultispan

end CategoryTheory.Limits
