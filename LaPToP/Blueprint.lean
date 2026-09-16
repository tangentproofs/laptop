import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LaPToP.Chapters.Prelude
import LaPToP.Chapters.BasicTheories
import LaPToP.Chapters.FunctionTheory
import LaPToP.Chapters.DataStructures
import LaPToP.Chapters.ProgramTheory
import LaPToP.Chapters.ProgrammingLanguage
import LaPToP.Chapters.RecursionConcurrency
import LaPToP.Chapters.TheoryDesign
import LaPToP.Chapters.Interaction
import LaPToP.Chapters.Collatz

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "LaPToP Blueprint" =>

This Blueprint tracks the Lean formalization of Eric Hehner's
*A Practical Theory of Programming* (LaPToP). Chapters follow the book's
major themes; a separate Collatz-style chapter is intentionally unfinished so
the generated graph and summary show an in-progress goal.

{include 0 LaPToP.Chapters.Prelude}
{include 0 LaPToP.Chapters.BasicTheories}
{include 0 LaPToP.Chapters.FunctionTheory}
{include 0 LaPToP.Chapters.DataStructures}
{include 0 LaPToP.Chapters.ProgramTheory}
{include 0 LaPToP.Chapters.ProgrammingLanguage}
{include 0 LaPToP.Chapters.RecursionConcurrency}
{include 0 LaPToP.Chapters.TheoryDesign}
{include 0 LaPToP.Chapters.Interaction}
{include 0 LaPToP.Chapters.Collatz}

{blueprint_graph}
{blueprint_summary}
