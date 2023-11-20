/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import MySql.SQLDSL

open Lean Elab Meta

namespace MySql

declare_syntax_cat      parsId
syntax ident          : parsId
syntax "(" parsId ")" : parsId

declare_syntax_cat           selectField
syntax parsId              : selectField
syntax parsId " AS " ident : selectField

declare_syntax_cat                 sqlSelect
syntax "*"                       : sqlSelect
syntax "DISTINCT " "*"           : sqlSelect
syntax selectField,+             : sqlSelect
syntax "DISTINCT " selectField,+ : sqlSelect

declare_syntax_cat                       entry
syntax "$`_"                           : entry
syntax "$`" noWs ident                 : entry
syntax "$`(" term ")"                  : entry
syntax "sorry"                         : entry
syntax "NULL"                          : entry
syntax "(" entry ")"                   : entry
syntax num                             : entry
syntax num &"u8"                       : entry
syntax num &"u16"                      : entry
syntax num &"u24"                      : entry
syntax num &"u32"                      : entry
syntax num &"u64"                      : entry
syntax "-" noWs num                    : entry
syntax "-" noWs num &"u8"              : entry
syntax "-" noWs num &"u16"             : entry
syntax "-" noWs num &"u32"             : entry
syntax "-" noWs num &"u64"             : entry
syntax scientific                      : entry
syntax scientific &"f32"               : entry
syntax scientific &"f64"               : entry
syntax "-" noWs scientific             : entry
syntax "-" noWs scientific &"f32"      : entry
syntax "-" noWs scientific &"f64"      : entry
syntax str                             : entry

declare_syntax_cat propSymbol
syntax " = "     : propSymbol
syntax " <> "    : propSymbol
syntax " != "    : propSymbol
syntax " < "     : propSymbol
syntax " <= "    : propSymbol
syntax " > "     : propSymbol
syntax " >= "    : propSymbol

declare_syntax_cat                prop
syntax "TRUE"                   : prop
syntax "FALSE"                  : prop
syntax parsId propSymbol parsId : prop
syntax parsId propSymbol entry  : prop
syntax prop " AND " prop        : prop
syntax prop " OR "  prop        : prop
syntax " NOT " prop             : prop
syntax "(" prop ")"             : prop

declare_syntax_cat join
syntax " INNER " : join
syntax " LEFT "  : join
syntax " RIGHT " : join
syntax " OUTER " : join

declare_syntax_cat                                 sqlFrom
syntax ident                                     : sqlFrom
syntax sqlFrom ", " sqlFrom                      : sqlFrom
syntax sqlFrom " AS " ident                      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop : sqlFrom
syntax "(" sqlFrom ")"                           : sqlFrom

syntax (name := query) "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)? : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabStrOfParsId : Syntax → TermElabM Expr
  | `(parsId|$id:ident)      => pure $ mkStrLit id.getId.toString
  | `(parsId|($pars:parsId)) => elabStrOfParsId pars
  | _                        => throwUnsupportedSyntax

def elabCol : TSyntax `selectField → TermElabM Expr
  | `(selectField|$c:parsId)             => do
    mkAppM ``MySql.SQLSelectField.col #[← elabStrOfParsId c]
  | `(selectField|$c:parsId AS $a:ident) => do
    mkAppM ``MySql.SQLSelectField.alias #[← elabStrOfParsId c, mkStrOfIdent a]
  | _                                    => throwUnsupportedSyntax

def elabSelect : Syntax → TermElabM Expr
  | `(sqlSelect|*)                          => mkAppM ``MySql.SQLSelect.all #[mkConst ``false]
  | `(sqlSelect|DISTINCT *)                 => mkAppM ``MySql.SQLSelect.all #[mkConst ``true]
  | `(sqlSelect|$cs:selectField,*)          => do
    let cols ← mkListLit (mkConst ``MySql.SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    mkAppM ``MySql.SQLSelect.list #[mkConst ``false, cols]
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let cols ← mkListLit (mkConst ``MySql.SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    mkAppM ``MySql.SQLSelect.list #[mkConst ``true, cols]
  | _                                       => throwUnsupportedSyntax

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

protected
def negFloat32 (f : Pod.Float32) : Pod.Float32 :=
  -1.0 * f

protected
def negFloat (f : Float) : Float :=
  -1.0 * f

protected
def mediumintOfNat (n : Nat) : DataEntry :=
  let n' := n % 2 ^ 24
  have : n' < 2 ^ 24 := Nat.mod_lt n (by decide)
  .mediumint ⟨n', Nat.lt_trans this (by decide)⟩ this

protected
def negInt8OfNat : Nat → UInt8 :=
  Pod.Int8.val ∘ Pod.instNegInt8.neg ∘ Pod.Int8.mk ∘ UInt8.ofNat

protected
def negInt16OfNat : Nat → UInt16 :=
  Pod.Int16.val ∘ Pod.instNegInt16.neg ∘ Pod.Int16.mk ∘ UInt16.ofNat

protected
def negInt32OfNat : Nat → UInt32 :=
  Pod.Int32.val ∘ Pod.instNegInt32.neg ∘ Pod.Int32.mk ∘ UInt32.ofNat

protected
def negInt64OfNat : Nat → UInt64 :=
  Pod.Int64.val ∘ Pod.instNegInt64.neg ∘ Pod.Int64.mk ∘ UInt64.ofNat

partial def elabEntry : TSyntax `entry → TermElabM Expr
  | `(entry|$`_) => mkFreshExprMVar (some $ mkConst ``MySql.DataEntry)
  | `(entry|$`$v) => Term.elabIdent v (some $ mkConst ``MySql.DataEntry)
  | `(entry|$`($v)) => Term.elabTerm v (some $ mkConst ``MySql.DataEntry)
  | `(entry|sorry) => mkSorry (mkConst ``MySql.DataEntry) false
  | `(entry|NULL) => elabConst ``MySql.DataEntry.null
  | `(entry|($e:entry)) => elabEntry e
  | `(entry|$v:num) =>
    mkAppM ``MySql.DataEntry.int #[mkApp' ``UInt32.ofNat (mkNatLit v.getNat)]
  | `(entry|$v:num u8) =>
    mkAppM ``MySql.DataEntry.tinyint #[mkApp' ``UInt8.ofNat (mkNatLit v.getNat)]
  | `(entry|$v:num u16) =>
    mkAppM ``MySql.DataEntry.smallint #[mkApp' ``UInt16.ofNat (mkNatLit v.getNat)]
  | `(entry|$v:num u24) =>
    mkAppM ``MySql.DataEntry.mediumint #[mkApp' ``MySql.mediumintOfNat (mkNatLit v.getNat)]
  | `(entry|$v:num u32) =>
    mkAppM ``MySql.DataEntry.int #[mkApp' ``UInt32.ofNat (mkNatLit v.getNat)]
  | `(entry|$v:num u64) =>
    mkAppM ``MySql.DataEntry.bigint #[mkApp' ``UInt64.ofNat (mkNatLit v.getNat)]
  | `(entry|-$v:num) =>
    mkAppM ``MySql.DataEntry.int #[mkApp' ``MySql.negInt32OfNat (mkNatLit v.getNat)]
  | `(entry|-$v:num u8) =>
    mkAppM ``MySql.DataEntry.tinyint #[mkApp' ``MySql.negInt8OfNat (mkNatLit v.getNat)]
  | `(entry|-$v:num u16) =>
    mkAppM ``MySql.DataEntry.smallint #[mkApp' ``MySql.negInt16OfNat (mkNatLit v.getNat)]
  | `(entry|-$v:num u32) =>
    mkAppM ``MySql.DataEntry.int #[mkApp' ``MySql.negInt32OfNat (mkNatLit v.getNat)]
  | `(entry|-$v:num u64) =>
    mkAppM ``MySql.DataEntry.bigint #[mkApp' ``MySql.negInt64OfNat (mkNatLit v.getNat)]
  | `(entry|$v:scientific) => do
    mkAppM ``MySql.DataEntry.double #[← Term.elabScientificLit v (mkConst ``Float)]
  | `(entry|$v:scientific f32) => do
    mkAppM ``MySql.DataEntry.float #[← Term.elabScientificLit v (mkConst ``Pod.Float32)]
  | `(entry|$v:scientific f64) => do
    mkAppM ``MySql.DataEntry.double #[← Term.elabScientificLit v (mkConst ``Float)]
  | `(entry|-$v:scientific) => do
    let f ← Term.elabScientificLit v (mkConst ``Float)
    mkAppM ``MySql.DataEntry.double #[mkApp' ``MySql.negFloat f]
  | `(entry|-$v:scientific f32) => do
    let f ← Term.elabScientificLit v (mkConst ``Pod.Float32)
    mkAppM ``MySql.DataEntry.float #[mkApp' ``MySql.negFloat32 f]
  | `(entry|-$v:scientific f64) => do
    let f ← Term.elabScientificLit v (mkConst ``Float)
    mkAppM ``MySql.DataEntry.double #[mkApp' ``MySql.negFloat f]
  | `(entry|$v:str) =>
    mkAppM ``MySql.DataEntry.varchar #[mkStrLit v.getString]
  | _ => throwUnsupportedSyntax

def elabPropSymbol (stx : Syntax) (isEntry : Bool) : TermElabM Name :=
  match stx with
  | `(propSymbol|=)  => pure $ if isEntry then ``MySql.SQLProp.eqE else ``MySql.SQLProp.eqC
  | `(propSymbol|<>) => pure $ if isEntry then ``MySql.SQLProp.neE else ``MySql.SQLProp.neC
  | `(propSymbol|!=) => pure $ if isEntry then ``MySql.SQLProp.neE else ``MySql.SQLProp.neC
  | `(propSymbol|<)  => pure $ if isEntry then ``MySql.SQLProp.ltE else ``MySql.SQLProp.ltC
  | `(propSymbol|<=) => pure $ if isEntry then ``MySql.SQLProp.leE else ``MySql.SQLProp.leC
  | `(propSymbol|>)  => pure $ if isEntry then ``MySql.SQLProp.gtE else ``MySql.SQLProp.gtC
  | `(propSymbol|>=) => pure $ if isEntry then ``MySql.SQLProp.geE else ``MySql.SQLProp.geC
  | _                => throwUnsupportedSyntax

partial def elabProp : Syntax → TermElabM Expr
  | `(prop|TRUE)                              => elabConst ``MySql.SQLProp.tt
  | `(prop|FALSE)                             => elabConst ``MySql.SQLProp.ff
  | `(prop|$l:parsId $s:propSymbol $r:parsId) => do
    mkAppM (← elabPropSymbol s false) #[← elabStrOfParsId l, ← elabStrOfParsId r]
  | `(prop|$c:parsId $s:propSymbol $e:entry)  => do
    mkAppM (← elabPropSymbol s true) #[← elabStrOfParsId c, ← elabEntry e]
  | `(prop|$l:prop AND $r:prop)               => do
    mkAppM ``MySql.SQLProp.and #[← elabProp l, ← elabProp r]
  | `(prop|$l:prop OR $r:prop)                => do
    mkAppM ``MySql.SQLProp.or #[← elabProp l, ← elabProp r]
  | `(prop|NOT $p:prop)                       => do
    mkAppM ``MySql.SQLProp.not #[← elabProp p]
  | `(prop|($p:prop))                         => elabProp p
  | _                                         => throwUnsupportedSyntax

def elabJoin : Syntax → TermElabM Expr
  | `(join|INNER) => elabConst ``MySql.SQLJoin.inner
  | `(join|LEFT)  => elabConst ``MySql.SQLJoin.left
  | `(join|RIGHT) => elabConst ``MySql.SQLJoin.right
  | `(join|OUTER) => elabConst ``MySql.SQLJoin.outer
  | _             => throwUnsupportedSyntax

partial def elabFrom : Syntax → TermElabM Expr
  | `(sqlFrom|$t:ident)               => mkAppM ``MySql.SQLFrom.table #[mkStrOfIdent t]
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    mkAppM ``MySql.SQLFrom.alias #[← elabFrom f, mkStrOfIdent t]
  | `(sqlFrom|$t₁:sqlFrom, $t₂:sqlFrom) => do mkAppM ``MySql.SQLFrom.implicitJoin #[← elabFrom t₁, ← elabFrom t₂]
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    mkAppM ``MySql.SQLFrom.join #[← elabJoin j, ← elabFrom l, ← elabFrom r, ← elabProp p]
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | _                                 => throwUnsupportedSyntax

@[term_elab query] def elabQuery : Term.TermElab := fun stx _ =>
  match stx with
  | `(query| SELECT $sel FROM $frm $[WHERE $prp]?) => do
    let whr ← match prp with
    | none     => elabConst ``MySql.SQLProp.tt
    | some prp => elabProp prp
    mkAppM ``MySql.SQLQuery.mk #[← elabSelect sel, ← elabFrom frm, whr]
  | _ => throwUnsupportedSyntax
