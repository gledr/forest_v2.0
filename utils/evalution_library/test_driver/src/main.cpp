#include <iostream>

#include "interface.hpp"

int main(int argc, char **argv) {
  std::cout << "Easy test driver to determine functionality of the interface module of the eval lib" << std::endl;
  
	__VERIFIER_nondet_bool("select_enable");
	__VERIFIER_nondet_int("select_value");
	__VERIFIER_nondet_bool("select_enable1");
	__VERIFIER_nondet_int("select_value2");
	__VERIFIER_nondet_bool("select_enable4");
	__VERIFIER_nondet_int("select_value5");

	return 0;
}
