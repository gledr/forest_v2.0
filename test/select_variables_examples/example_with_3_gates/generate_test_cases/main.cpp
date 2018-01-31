#include <iostream>
#include <sstream>
#include <map>
#include <vector>
#include <fstream>
#include <cassert>

void get_header (std::stringstream & stream){
	stream << "void __VERIFIER_assert (int val);" << std::endl;
	stream << std::endl;
	stream << "int main () {" << std::endl;
	stream << std::endl;
}

void get_clauses(std::stringstream & stream){
	stream << "\t" << "int z1 = a & b;  // AND" << std::endl;
	stream << "\t" << "int z2 = b | c;  // XOR --> BUG is here" << std::endl;
	stream << "\t" << "int f = z1 | z2; // OR"  << std::endl;
	stream << std::endl;
	stream << "\t" <<   "__VERIFIER_assert(f == y);" << std::endl;
	stream << "}" << std::endl;
}

std::vector<std::map<std::string, std::string> > cases;

void fill_cases(){
	// case 1
	std::map<std::string, std::string> case_1;
	case_1["a"] = "0";
	case_1["b"] = "0";
	case_1["c"] = "0";
	case_1["y"] = "0";
	cases.push_back(case_1);

	// case 2
	std::map<std::string, std::string> case_2;
	case_2["a"] = "0";
	case_2["b"] = "0";
	case_2["c"] = "1";
	case_2["y"] = "1";
	cases.push_back(case_2);

	// case 3
	std::map<std::string, std::string> case_3;
	case_3["a"] = "0";
	case_3["b"] = "1";
	case_3["c"] = "0";
	case_3["y"] = "1";
	cases.push_back(case_3);

	// case 4
	std::map<std::string, std::string> case_4;
	case_4["a"] = "0";
	case_4["b"] = "1";
	case_4["c"] = "1";
	case_4["y"] = "0";
	cases.push_back(case_4);


	 // case 5
	std::map<std::string, std::string> case_5;
	case_5["a"] = "1";
	case_5["b"] = "0";
	case_5["c"] = "0";
	case_5["y"] = "0";
	cases.push_back(case_5);

	// case 6
	std::map<std::string, std::string> case_6;
	case_6["a"] = "1";
	case_6["b"] = "0";
	case_6["c"] = "1";
	case_6["y"] = "1";
	cases.push_back(case_6);


	// case 7
	std::map<std::string, std::string> case_7;
	case_7["a"] = "1";
	case_7["b"] = "1";
	case_7["c"] = "0";
	case_7["y"] = "1";
	cases.push_back(case_7);

	// case 8
	std::map<std::string, std::string> case_8;
	case_8["a"] = "1";
	case_8["b"] = "1";
	case_8["c"] = "1";
	case_8["y"] = "1";
	cases.push_back(case_8);
}

void get_case(int _case, std::stringstream & stream){
	std::string a = cases[_case]["a"];
	std::cout << a <<  std::endl;
	stream << "\tint a = " << a << ";" << std::endl;
	stream << "\tint b = " << cases[_case]["b"] << ";" << std::endl;
	stream << "\tint c = " << cases[_case]["c"] << ";" << std::endl;
	stream << "\tint y = " << cases[_case]["y"] << ";" << std::endl;
	stream << std::endl;
}


int main (int argc, char * argv[]) {
	std::stringstream file;
	fill_cases();
	get_header(file);
	std::stringstream cast_me;
	cast_me << argv[1];
	int _case;
	cast_me >> _case;
	assert (cases.size() >= _case);
	get_case(_case, file);
	get_clauses(file);
	std::cout << file.str() << std::endl;
	std::fstream out_file;
	out_file.open("main.c", std::ios::out);
	out_file << file.str();
	out_file.close();
	return 0;
}
