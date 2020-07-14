# Mechanized Formal Model of Bitcoin's Blockchain Validation Procedures
Kristijan Rupić (kristijan.rupic@fer.hr), Lovro Rožić (lorozic33@gmail.com), and Ante Đerek (ante.derek@fer.hr)
[Faculty of Electrical Engineering and Computing, University of Zagreb](https://www.fer.unizg.hr/en)

This is the Coq artifact of our paper "Mechanized Formal Model of Bitcoin's Blockchain Validation Procedures"
submitted to [FMBC 2020](https://fmbc.gitlab.io/2020/).

## Compiling

Run `coq_makefile -f _CoqProject -o makefile` and then `make`.

Utils.v has to be compiled before Bitcoin.v works. Checked with Coq version 8.10.2.
