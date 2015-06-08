# qcalgebra
Quantum Computing Algebra package. Quite symbolic. Written in J

- K0 is |0>
- K1 is |1>

The qubits are expressed via boxed set. So, for example,

- 1;0 0 (boxed) means |00>
- 1;0 1 0 means |010>
- etc...

The operator are written in CAPITAL LETTERS:

- HD : Hadamard Gate acting on qubit x of quantum state y, i.e. 0 HD K00
       it means Hadamard gate acting on the first qubit (qubit 0) of |00>
- XG, YG, ZG: Pauli Gates. The same behaviour as described for HD
- CNOT : Controlled NOT (XG) gate. Use: (c,t) CNOT qreg, where c is control qubit
         and t is target qubit
- CY, CZ : Controlled Y and Controlled Z. As above.

There are some other interesting functions:

- simpl : it performs simplification of qubit expression (summation and
          cleaning of small amplitudes)
- PROB : it extracts the probability related to measurement of bits in the qreg,
         i.e. (0;1 1) 0 HD K00 - it returns the probability to have as result of
         measurement the first two qubit to 1, so all the states: |11?>. The first
         element in the boxed list is the offset (0-based) for the qubit pattern.
