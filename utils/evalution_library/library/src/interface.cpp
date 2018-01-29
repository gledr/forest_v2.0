#include <iostream>
#include <sqlite3.h>
#include <vector>
#include <cassert>
#include <map>

#include "interface.hpp"

struct SingleResult {
	std::string value;
	int problem_id;
};

std::map<std::string, std::vector<SingleResult>> results;

static int callback(void *data, int argc, char **argv, char **azColName);
static std::string const DB_PATH = "/dev/shm/forest/database.db";

static void run_init();

static bool init_done = false;

static std::string get_mangled_name (std::string const & name);

void __VERIFIER_assert(int val){
  std::cout << "__VERIFIER_assert has been called..." << std::endl;
  if (val){
	std::cout << "Solution is SAT" << std::endl;
  } else {
	std::cout << "Solution is UNSAT" << std::endl;
  }
}

int __VERIFIER_nondet_int(char * _reg_name){
  std::cout << "__VERIFIER_nondet_int" << std::endl;
  std::cout << _reg_name << std::endl;
	if(!init_done){
		run_init();
	}
	std::string reg_name = get_mangled_name(_reg_name);
	static size_t cnt = 0;
	if (cnt < results[reg_name].size()){
	   std::cout << results[reg_name][cnt].value << std::endl;
		int answer = std::stoi(results[reg_name][cnt].value);
		cnt++;
		std::cout << "Injection Value: " << answer << std::endl;
		return answer;
	} else {
		std::cerr << "Index Error: cnt > select_values.size()" << std::endl;
		return false;
	}
}

bool __VERIFIER_nondet_bool(char * _reg_name){
  std::cout << "__VERIFIER_nondet_bool" << std::endl;
	std::cout << _reg_name << std::endl;
	if(!init_done){
		run_init();
	}
	std::string reg_name = get_mangled_name(_reg_name);
	static size_t cnt = 0;
	std::cout << cnt << std::endl;
	if (cnt < results[reg_name].size()){
		bool answer;
		if (results[reg_name][cnt].value == "true" || results[reg_name][cnt].value == "1"){
			answer = true;
		} else {
			answer = false;
		}
		std::cout << "Injection Select Value: " << answer << std::endl;
		cnt++;
		return answer;
	} else {
		std::cerr << "Index Error: cnt > select_variables.size()" << std::endl;
		return false;
	}
}

int callback(void *data, int argc, char **argv, char **azColName){

	if(results.find(argv[1]) == results.end()){
		results.insert(std::pair<std::string, std::vector<SingleResult> >(argv[1], std::vector<SingleResult>()));
	}
	SingleResult res;
	res.value = argv[0];
	res.problem_id = std::stoi(argv[2]);
	results[argv[1]].push_back(res);

	std::cout << "Inserting " << argv[1] << " with value " << argv[0] << std::endl;

	return 0;
 }

static void run_init(){
	try{
		sqlite3 * db;
		char * error_msg = 0;
		std::string query = "SELECT value, name_hint, problem_id FROM results;";

		if(sqlite3_open(DB_PATH.c_str(), &db) != 0){
			std::string error_msg = "Could now open database: " + DB_PATH;
			throw std::runtime_error(error_msg);
		}
		if(sqlite3_exec(db, query.c_str(), callback, NULL , &error_msg) != 0){
			std::string error_msg = "Can not execute query: " + query;
			throw std::runtime_error(error_msg);
		}
		if (sqlite3_close(db) != 0){
			std::string error_msg = "Can not close database (" + DB_PATH + ")";
			throw std::runtime_error(error_msg);
		}
		init_done = true;
	}catch (std::runtime_error const & msg){
		std::cerr << msg.what() << std::endl;
	}
}

static std::string get_mangled_name (std::string const & name){
  return "main_register_" + name;
}
