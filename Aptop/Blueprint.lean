import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Aptop.Chapters.Prelude
import Aptop.Chapters.BasicTheories
import Aptop.Chapters.FunctionTheory
import Aptop.Chapters.DataStructures
import Aptop.Chapters.ProgramTheory
import Aptop.Chapters.ProgrammingLanguage
import Aptop.Chapters.RecursionConcurrency
import Aptop.Chapters.TheoryDesign
import Aptop.Chapters.Interaction
import Aptop.Chapters.Collatz

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Aptop Blueprint" =>

This Blueprint tracks the Lean formalization of Eric Hehner's
*A Practical Theory of Programming* (Aptop). Chapters follow the book's
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
asserted that is not proved. Chapter 10's exercises live in `Aptop/Exercises/`
(not Blueprint nodes): formalized and proved section by section, the rest still
deferred stubs, as `MISSING.md` §5 counts.
Gaps that are not formalized on purpose are listed in `MISSING.md`. The Collatz
chapter records the proved Exercise 255 timing development only.

{include 0 Aptop.Chapters.Prelude}
{include 0 Aptop.Chapters.BasicTheories}
{include 0 Aptop.Chapters.FunctionTheory}
{include 0 Aptop.Chapters.DataStructures}
{include 0 Aptop.Chapters.ProgramTheory}
{include 0 Aptop.Chapters.ProgrammingLanguage}
{include 0 Aptop.Chapters.RecursionConcurrency}
{include 0 Aptop.Chapters.TheoryDesign}
{include 0 Aptop.Chapters.Interaction}
{include 0 Aptop.Chapters.Collatz}

{blueprint_graph}
{blueprint_summary}
