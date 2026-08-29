/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init

/-!
# `ToExpr` instances for Mathlib
-/

public meta section

namespace Mathlib
open Lean

set_option autoImplicit true in
deriving instance ToExpr for ULift

universe u in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ToLevel.{u}]
  signature: : ToExpr PUnit.{u+1} where
  body: mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax

中文:
实例 [ToLevel.{u}]
  签名: : ToExpr PUnit.{u+1} where
  定义体: mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax

Depends on / 依赖: PUnit.unit, mkConst, toLevel
-/
instance [ToLevel.{u}] : ToExpr PUnit.{u+1} where
  toExpr _ := mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax

open DataValue in
/--
Definition of `toExprMData` / `toExprMData` 的定义

English:
definition toExprMData
  signature: (md : MData)
  body: Id.run do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := toExpr k
    e := match v with
          | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
          | ofBool v => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
          | ofName v => mkApp3 (mkCon

中文:
定义 toExprMData
  签名: (md : MData)
  定义体: Id.run do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := toExpr k
    e := match v with
          | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
          | ofBool v => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
          | ofName v => mkApp3 (mkCon
-/
private def toExprMData (md : MData) : Expr := Id.run do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := toExpr k
    e := match v with
          | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
          | ofBool v => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
          | ofName v => mkApp3 (mkConst ``KVMap.setName) e k (toExpr v)
          | ofNat v => mkApp3 (mkConst ``KVMap.setNat) e k (mkNatLit v)
          | ofInt v => mkApp3 (mkConst ``KVMap.setInt) e k (toExpr v)
          | ofSyntax v => mkApp3 (mkConst ``KVMap.setSyntax) e k (toExpr v)
  return e

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToExpr MData
  body: toExprMData
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Expr

中文:
实例 :
  签名: ToExpr MData
  定义体: toExprMData
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Expr

Depends on / 依赖: toExprMData
-/
instance : ToExpr MData where
  toExpr := toExprMData
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Expr

end Mathlib
