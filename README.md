Mirror Shard
============

Contact
-------
Gregory Malecha <gmalecha@cs.harvard.edu>

Purpose
-------

This repository contains a framework for building reflective decision
procedures in Coq. It is currently focused on automating separation
logic entailments though the pieces used for this are reusable for a
wide variety of applications.

Components
----------

Reflective Theorem Provers
 
  An interface, and several simple implementations, of reflective
  theory provers. These exist to support reasoning that would usually
  be done in Ltac since Ltac programs can not be called from Gallina. 

Expression Unification
 
  Supports syntactic unification of reflected expressions. This
  enables matching for predicate refinement and cancellation. 

Predicate Refinement (Unfolder)

  Applies separation logic lemmas (in the form of P ===> Q) to
  separation logic formulae in either a forward or backward
  direction. Pure premises of the formula are discharged using the
  reflective theorem provers.

Cancelation

  Implements a separation logic implication simplifier based on
  repeated cancellation. The cancellation algorithm will choose
  unification variables (in Gallina) and therefore can make provable
  goals unprovable using its current heuristic.

These components have also been used to implement a symbolic execution
mechanism for the Bedrock intermediate language. Due to its dependency
on the core Bedrock, this symbolic executer has been removed from the
current versions of the repository. 

Building
--------

This release requires Coq 8.4pl1 (final released version) and coq-ext-lib.

1) In a separate directory, download and install coq-ext-lib from:
   https://github.com/coq-ext-lib/coq-ext-lib

2) To build, run

   make -jN

   from the command line (substituting 'N' for the number of parallel
   jobs to run).

3) To install, run

   make install

Using
-----

History
-------

The automation is an adaption and generalization of the automation
developed for the Bedrock programming library
(http://plv.csail.mit.edu/bedrock/).

