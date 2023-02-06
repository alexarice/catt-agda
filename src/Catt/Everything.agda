{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Everything where

import Catt.Prelude
import Catt.Prelude.Properties

import Catt.Syntax.Base
import Catt.Syntax
import Catt.Syntax.Bundles
import Catt.Syntax.SyntacticEquality

import Catt.Globular
import Catt.Globular.Properties

import Catt.Variables
import Catt.Variables.Properties

import Catt.Pasting
import Catt.Pasting.Properties

import Catt.Suspension
import Catt.Suspension.Properties
import Catt.Suspension.Pasting

import Catt.Connection
import Catt.Connection.Properties
import Catt.Connection.Pasting

import Catt.Tree
import Catt.Tree.Properties
import Catt.Tree.Pasting
import Catt.Tree.Unbiased
import Catt.Tree.Unbiased.Properties
import Catt.Tree.Insertion
import Catt.Tree.Insertion.Properties

import Catt.Dyck
import Catt.Dyck.Properties
import Catt.Dyck.Pruning
import Catt.Dyck.Pruning.Properties
import Catt.Dyck.FromTree

import Catt.Support
import Catt.Support.Properties
import Catt.Support.Context
import Catt.Suspension.Support
import Catt.Connection.Support
import Catt.Tree.Support
import Catt.Tree.Unbiased.Support
import Catt.Tree.Insertion.Support

import Catt.Discs
import Catt.Discs.Properties
import Catt.Discs.Support
import Catt.Discs.Pasting

import Catt.Typing.Base
import Catt.Typing
import Catt.Typing.Properties.Base
import Catt.Typing.Properties.Lifting
import Catt.Suspension.Typing
import Catt.Typing.Properties.Substitution
import Catt.Typing.Properties.Substitution.Suspended
import Catt.Typing.Properties
import Catt.Typing.Properties.Support
import Catt.Typing.Properties.Conversion
import Catt.Connection.Typing

import Catt.Tree.Typing
import Catt.Tree.Unbiased.Typing
import Catt.Tree.Insertion.Typing

import Catt.Dyck.Typing
import Catt.Dyck.Pruning.Typing

import Catt.Discs.Typing

-- import Catt.Strict.Assoc
-- import Catt.Typing.Weak

-- import Catt.Syntax.Complexity
