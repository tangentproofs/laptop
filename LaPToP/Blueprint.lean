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
major themes and cover every section of Chapters 1–9 of the book: the Prelude
is Binary Theory (Section 1.0), Basic Theories are Sections 1.0.1–2.1 together
with the Generic laws of the Reference chapter, Function Theory is Chapter 3
(including Section 3.4, limits and reals), Data Structures are Sections 2.2–2.3
(strings and lists) with functions as data, Program Theory is Chapter 4
(including Section 4.4, the old terminology), Programming Language is Chapter 5
(including probabilistic and functional programming), Recursion and Concurrency
are Chapters 6 and 8, Theory Design and Implementation is Chapter 7, and
Interaction is Chapter 9. The law tables of the Reference chapter (Section
11.3) are surveyed law by law in the repository file `.sci/laws-survey.md`:
each law is a Lean theorem named in a node, or the node explains why it is not
statable in this typed model (decimal notation, the type distinctions
between a bunch and its set or list packaging, bunch-valued operators,
multi-dimensional lists).
Every node quotes the book and points at sorry-free Lean declarations; where
the model departs from the book, adds a side condition, or corrects the book's
argument, the node prose and the module docstrings say so — nothing is
asserted that is not proved. Chapter 10 exercise *statements* live as deferred
stubs in `LaPToP/Exercises/` (signatures with `sorry` only; not Blueprint nodes).
Gaps that are not formalized on purpose are listed in `MISSING.md`. The Collatz
chapter records the proved Exercise 255 timing development only.

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
