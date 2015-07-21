# qcalgebra
Quantum Computing Algebra package. Quite symbolic. Written in J

- K0 is |0>
- K1 is |1>
- K00 is K0 TP K0, TP function is used to create bigger qubits (Tensor Product)

The qubits are expressed via boxed set (the first element is the complex coefficient). So, for example,

- 1;0 0 (boxed) means |00>
- 1;0 1 0 means |010>
- etc...

The operator are written in CAPITAL LETTERS:

- HD        : Hadamard Gate acting on qubit x of quantum state y, i.e. 0 HD K00
              it means Hadamard gate acting on the first qubit (qubit 0) of |00>
- XG, YG, ZG: Pauli Gates. They have the same behaviour as described for HD
- CNOT :      Controlled NOT (XG) gate. Use: (c,t) CNOT qreg, where c is control qubit
              and t is target qubit
- CY, CZ :    Controlled Y and Controlled Z. As above.
- R(phi) :    Phase shift gate
- R_k :       Phase shift gate modified for QFT
- CRK :       Controlled version of R_k

There are some other interesting functions:

- simpl : it performs simplification of qubit expression (summation and
          cleaning of small amplitudes)
- PROB  : it extracts the probability related to measurement of bits in the qreg,
         i.e. (0;1 1) 0 HD K00 - it returns the probability to have as result of
         measurement the first two qubit to 1, so all the states: |11?> after
         applying hadamard gate to the first qubit of |00>. The first element in
         the boxed list is the offset (0-based) for the qubit pattern.

- QFT   : performs the QFT (quantum fourier transform) on qubits.
          3 QFT K000 computes the QFT on the three first qubits of K000
 
- Added some QEC states (encoded logical states in 9 qubits), but more has to be developed (like decoding).
