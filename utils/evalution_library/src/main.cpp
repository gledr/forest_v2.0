#include <iostream>

#include "interface.hpp"

int main(int argc, char **argv) {
  std::cout << "Easy test driver to determine functionality of the interface module of the eval lib" << std::endl;
  
	int val =  __VERIFIER_nondet_bool("main_register_select_enable");
	std::cout << "Enable " << std::boolalpha << val << std::endl;
	int input =  __VERIFIER_nondet_int("main_register_select_value");
	std::cout << "Value: " << input  << __VERIFIER_nondet_int("main_register_select_value") << std::endl;

	return 0;
}
