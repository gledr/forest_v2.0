#include <iostream>
#include <sqlite3.h>
#include <vector>
#include <cassert>
#include <algorithm>
#include <iterator>
#include <sstream>

#include "interface.hpp"

#define DEBUG


/*
 * @brief Structure to represent on row of the results table in the db
 *
 */
struct SingleResult {
	std::string value;
	std::string name;
	size_t problem_id;
};

/*
 * @brief Structure to represent one specific found test case
 */
struct SingleProblem{
	std::vector<std::pair<std::string, std::string> > content;
	int id;

	/*
	 * @brief Operator needed to apply std::unique
	 */
	bool operator== (SingleProblem const & val){
		if (content == val.content){
			return true;
		} else {
			return false;
		}
	}
};

/*
 * @brief Global Variable to dump data from db in
 */
static std::vector<SingleResult> raw_data;

/*
 * @brief Global Variables to store all unique problems
 */
static std::vector<SingleProblem> data;

/*
 * @brief Path of database file
 */
static std::string const DB_PATH = "/dev/shm/forest/database.db";

/*
 * @brief Flag to indicate if the data from the db is ready or not
 */
static bool init_done = false;

/**
 * @brief Collect data from the database and preprocess it
 */
static void run_init();

/**
 * @brief Preprocess data from database
 */
static void preprocess_data();

/**
 * @brief Callback function used to execute SQL queries
 */
static int callback(void *, int argc, char **argv, char **azColName);

/*
 * @brief Returns the needed value for a certain problem for a certain register
 *
 * @param name The registers name
 * @param problem_id The current problem id
 * @return The value of the register
 */
static int get_injection_val(std::string const & name, size_t const problem_id);

/*
 * @brief Dump the data obtained from the db to an ostream
 *
 * @param strean The ostream to pipe the stream to
 */
static void dump_results(std::ostream & stream = std::cout);

void __VERIFIER_assert(int val){
  if(val){
	std::cout << "Problem is SAT" << std::endl;
  } else {
	std::cout << "Problem is UNSAT" << std::endl;
  }
}

int __VERIFIER_nondet_int(char * _reg_name){
	if(!init_done){
		run_init();
	}
	return get_injection_val(_reg_name, data.front().id);
}

bool __VERIFIER_nondet_bool(char * _reg_name){
	if(!init_done){
		run_init();
	}
	return get_injection_val(_reg_name, data.front().id);
}

void run_init(){
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
		preprocess_data();
		//dump_results();
		init_done = true;
	}catch (std::runtime_error const & msg){
		std::cerr << msg.what() << std::endl;
	}
}

void preprocess_data() {
	size_t num_of_problems = 0;
	for(std::vector<SingleResult>::iterator itor = raw_data.begin(); itor != raw_data.end(); ++itor){
		if(itor->problem_id > num_of_problems){
			num_of_problems = itor->problem_id;
		}
	}

	data.clear();
	data.resize(num_of_problems+1); // vector index starts at 0

	for(std::vector<SingleResult>::iterator itor = raw_data.begin(); itor != raw_data.end(); ++itor){
		std::pair<std::string,std::string> tmp;
		tmp.first = itor->name;
		tmp.second = itor->value;
		data[itor->problem_id].id = itor->problem_id;
		data[itor->problem_id].content.push_back(tmp);
	}

	// remove duplicates --> compare solving loops!
	data.erase(std::unique(data.begin(), data.end()), data.end());

	for(std::vector<SingleProblem>::iterator itor = data.begin(); itor != data.end(); ++itor){
		if(itor->content.empty()){
			data.erase(itor);
		}
	}
}

int callback(void *, int argc, char **argv, char **azColName){
	assert (argc == 3);

	SingleResult tmp;
	tmp.value = argv[0];
	tmp.name = argv[1];
	tmp.problem_id = std::stoi(argv[2]);
	raw_data.push_back(tmp);

	return 0;
 }

int get_injection_val(std::string const & name, size_t const problem_id){
	std::vector<std::pair<std::string, std::string> > problem;

	for(std::vector<SingleProblem>::iterator it = data.begin(); it != data.end(); ++it){
		if (static_cast<size_t>(it->id) == problem_id){
			problem = it->content;
		}
	}

	if (!problem.empty()){
		std::vector<std::pair<std::string, std::string> >::const_iterator itor;
			std::string value = "";
			for(itor = problem.begin(); itor != problem.end(); ++itor){
				if(itor->first == name){
					value = itor->second;
				}
			}

			if(value.empty()){
				std::cerr << "Could not find: " << name << " as identifier!" << std::endl;
				std::cerr << "Result will not be valid!" << std::endl;
			}

			// We can't convert a string containing T|F to bool via stringstream
			if(value == "true"){
				value = "1";
			} else if(value == "false"){
				value = "0";
			}
			std::stringstream sstream(value);

			// We can not make a tempplate argument here since clang is not as smart gcc and
			// interprets every positive number as 1 - however int for bool works aswell
			int ret_val;
			sstream >> ret_val;

#ifdef DEBUG
			std::cout << "#################################" << std::endl;
			std::cout << "Problem #" << problem_id << std::endl;
			std::cout << "Register: " << name << std::endl;
			std::cout << "Value: " << ret_val << std::endl;
			std::cout << "#################################" << std::endl;
#endif

		return ret_val;

	} else {
		std::cerr << "Problem Number: " << problem_id << "not recognized..." << std::endl;
		return -1;
	}
}

void dump_results(std::ostream & stream){
	std::vector<std::pair<std::string, std::string> >::const_iterator itor;
	for(size_t i = 0; i < data.size(); ++i){
		if(!data[i].content.empty()){
			stream << "Problem ID: " << data[i].id << std::endl;
			for(itor = data[i].content.begin(); itor != data[i].content.end(); ++itor){
				stream << "Name: " << itor->first << std::endl;
				stream << "Value: " << itor->second << std::endl;
			}
		}
	}
}
