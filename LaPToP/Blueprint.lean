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
major themes and cover Chapters 1–9 of the book: the Prelude is Binary Theory
(Section 1.0), Basic Theories are Sections 1.0.1–2.1, Function Theory is
Chapter 3, Data Structures are Sections 2.2–2.3 (strings and lists) with
functions as data, Program Theory is Chapter 4, Programming Language is
Chapter 5, Recursion and Concurrency are Chapters 6 and 8, Theory Design and
Implementation is Chapter 7, and Interaction is Chapter 9. Every node quotes
the book and points at sorry-free Lean declarations; where the model departs
from the book, or the book's argument is corrected or left unproved, the node
prose and the module docstrings say so. A separate Collatz-style chapter is
intentionally unfinished so the generated graph and summary show an
in-progress goal.

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
