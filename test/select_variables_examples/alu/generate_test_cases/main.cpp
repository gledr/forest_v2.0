#include <iostream>
#include <sstream>
#include <map>
#include <vector>
#include <fstream>
#include <cassert>

#define ADD "ADD"
#define SUB "SUB"
#define INC "INC"
#define DEC "DEC"

void get_header (std::stringstream & stream){
  std::fstream file("head.c", std::ios::in);
  std::string line;
  while(std::getline(file, line)){
	stream << line << std::endl;
  }
  file.close();
}

void get_clauses(std::stringstream & stream){
  std::fstream file("clauses.c", std::ios::in);
  std::string line;
  while(std::getline(file, line)){
	stream << line << std::endl;
  }
}

std::vector<std::map<std::string, std::string> > cases;

void fill_cases(){
  {
	// case 1
	std::map<std::string, std::string> case_1;
	case_1["c_side_a_in"] = "2";
	case_1["c_side_b_in"] = "2";
	case_1["c_opcode_in"] = ADD;
	case_1["c_expected_out"] = "4";
	case_1["c_expected_zero_out"] = "0";
	cases.push_back(case_1);
  }
  {
	// case 2
	std::map<std::string, std::string> case_2;
	case_2["c_side_a_in"] = "0";
	case_2["c_side_b_in"] = "1";
	case_2["c_opcode_in"] = ADD;
	case_2["c_expected_out"] = "1";
	case_2["c_expected_zero_out"] = "0";
	cases.push_back(case_2);
  }
  {
		// case 3
	std::map<std::string, std::string> case_3;
	case_3["c_side_a_in"] = "2";
	case_3["c_side_b_in"] = "2";
	case_3["c_opcode_in"] = SUB;
	case_3["c_expected_out"] = "0";
	case_3["c_expected_zero_out"] = "1";
	cases.push_back(case_3);
  }
  {
		// case 4
	std::map<std::string, std::string> case_4;
	case_4["c_side_a_in"] = "2";
	case_4["c_side_b_in"] = "1";
	case_4["c_opcode_in"] = SUB;
	case_4["c_expected_out"] = "1";
	case_4["c_expected_zero_out"] = "0";
	cases.push_back(case_4);
  }
  {
		// case 5
	std::map<std::string, std::string> case_5;
	case_5["c_side_a_in"] = "1";
	case_5["c_side_b_in"] = "1";
	case_5["c_opcode_in"] = INC;
	case_5["c_expected_out"] = "2";
	case_5["c_expected_zero_out"] = "0";
	cases.push_back(case_5);
  }
  {
   	// case 6
	std::map<std::string, std::string> case_6;
	case_6["c_side_a_in"] = "0";
	case_6["c_side_b_in"] = "0";
	case_6["c_opcode_in"] = INC;
	case_6["c_expected_out"] = "1";
		case_6["c_expected_zero_out"] = "0";
	cases.push_back(case_6);
  }
  {
		// case 7
	std::map<std::string, std::string> case_7;
	case_7["c_side_a_in"] = "1";
	case_7["c_side_b_in"] = "1";
	case_7["c_opcode_in"] = DEC;
	case_7["c_expected_out"] = "0";
	case_7["c_expected_zero_out"] = "1";
	cases.push_back(case_7);
  }
  {
		// case 8
	std::map<std::string, std::string> case_8;
	case_8["c_side_a_in"] = "2";
	case_8["c_side_b_in"] = "2";
	case_8["c_opcode_in"] = DEC;
	case_8["c_expected_out"] = "1";
	case_8["c_expected_zero_out"] = "1";
	cases.push_back(case_8);
  }
}

void get_case(int _case, std::stringstream & stream){
  std::cout << _case << std::endl;
	std::string a = cases[_case]["c_side_a_in"];
	std::cout << a <<  std::endl;
	stream << "\tint c_side_a_in = " << a << ";" << std::endl;
	stream << "\tint c_side_b_in = " << cases[_case]["c_side_b_in"] << ";" << std::endl;
	stream << "\tint c_opcode_in = " << cases[_case]["c_opcode_in"] << ";" << std::endl;
	stream << "\tint c_expected_out = " << cases[_case]["c_expected_out"] << ";" << std::endl;
	stream << "\tint c_expected_zero_out = " << cases[_case]["c_expected_zero_out"] << ";" << std::endl;
	stream << "\tint result_out = 0;" << std::endl;
	stream <<"\tint zero_out;" << std::endl;
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
