#ifndef INTERFACE_HPP_
#define INTERFACE_HPP_

/*
 * @brief Verify a found Result from Forest to be correct
 *
 * Function to be called after results found by Forest have been
 * inserted in to the code and executed.
 *
 * @param val Variable to determine if solution is SAT or UNSAT
 */
extern "C" void __VERIFIER_assert(int val);

/*
 * @brief Inject a certain integer value into LLVM-IR
 *
 * After Forest has showed up with a solution stored into
 * the database, this function has to be called to access the
 * db and to inject the result into the LLVM-IR
 *
 * @param _reg_name The register for which the solution has to be injected
 * @return The value to be injected
 */
extern "C" int __VERIFIER_nondet_int(char * _reg_name);

/*
 * @brief Inject a certain bool value into LLVM-IR
 *
 * After Forest has showed up with a solution stored into
 * the database, this function has to be called to access the
 * db and to inject the result into the LLVM-IR
 *
 * @param _reg_name The register for which the solution has to be injected
 * @return The value to be injected
 */
extern "C" bool __VERIFIER_nondet_bool(char * _reg_name);

#endif /* INTERFACE_HPP_ */

