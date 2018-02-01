#ifndef DATABASEEXPORTER_HPP_
#define DATABASEEXPORTER_HPP_

#include <iostream>
#include <iomanip>
#include <string>
#include <sqlite3.h>
#include <boost/filesystem.hpp>
#include <vector>
#include <set>
#include <regex>
#include <map>

#define DEBUG


/**
 * @brief Export Database Information into smt2 format
 * Export collected data of multiple forest runs to cover
 * - all paths
 * - multiple use cases in one file
 */
class DatabaseExporter {
public:
  /**
   * @brief CTOR
   *
   * @param path Database-File
   */
  DatabaseExporter(std::string path){
	p_db = 0;
	p_path = path;
	p_active_transition = init;
	p_num_of_problems = 0;
  }

  /**
   * @brief DTOR
   */
  ~DatabaseExporter(){
	sqlite3_close(p_db);
  }

  /**
   * @brief Set target directory absolute
   *
   * @param dir The directory to use, create if not existing
   */
  void set_directory(std::string dir){
	p_root_dir = dir;
  }


  /**
   * @brief Open Connection to database
   */
  void OpenDatabase () {
	int success = -1;
	try {
	  if((success = sqlite3_open(p_path.c_str(), &p_db)) != 0){
		throw new std::runtime_error("Can not open database!");
	  }
#ifdef DEBUG
	  std::cout << "Database Connection Established!" << std::endl;
#endif
	} catch (std::runtime_error & err){
	  std::cerr<< err.what() << std::endl;
	}
  }

  /**
   * @brief Collect Data From Database
   */
  void collect_data(){
	this->get_model_assertions();
	this->get_free_variables();
  }

  /**
   * @param Callback forward function for the sqlite callback
   *
   * #FIXME: Make it a friend and not public!
   */
  int __callback__(int argc, char **argv, char **azColName){
	try {
	  if (p_active_transition == free_variables){
		assert (argc == 3);
		FreeVariables table_entry;
		table_entry.reg_name = argv[0];
		table_entry.resolved_name = argv[1];
		table_entry.type = argv[2];
		table_entry.used = false;

		if(std::find(p_free_variables.begin(), p_free_variables.end(), table_entry) == p_free_variables.end()){
		  p_free_variables.push_back(table_entry);
		}
		std::cout << "Callback done " << std::endl;
	  } else if (p_active_transition == assertions){
		p_assertions.push_back(argv[0]);
	  }
	} catch (...){
	  std::cerr<< "Unknown error caught!" << std::endl;
	}
	return 0;
  }

  /**
   * @brief Dump the Free Variables to any stream
   *
   * @param stream The stream to pipe the data to. Standard: std::cout
   */
  void print_free_variables(std::ostream & stream = std::cout){
	size_t max_reg = 0;
	size_t max_resol = 0;
	size_t max_type = 0;
	size_t const overhead = 5;
	size_t const blanks = 2;

	std::vector<FreeVariables>::iterator itor;
	for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  if (itor->reg_name.size() > max_reg){
		max_reg = itor->reg_name.size();
	  }
	  if (itor->resolved_name.size() > max_resol){
		max_resol = itor->resolved_name.size();
	  }
	  if(itor->type.size() > max_type){
		max_type = itor->type.size();
	  }
	}

	stream << std::string(max_reg + max_resol + max_type + overhead + blanks+3, '#') << std::endl;
	std::string const header = "free variables";
	size_t pre_post_header = (max_reg + max_resol + max_type + overhead - header.size())/2;
	stream << std::string(pre_post_header+blanks, '#') << " " << header << " " << std::string(pre_post_header+blanks, '#') << std::endl;
	stream << std::string(max_reg + max_resol + max_type + overhead + blanks+3, '#') << std::endl;

	for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  stream << std::left
			 << std::setw(max_reg)
			 << itor->reg_name
			 << std::string(overhead, ' ')
			 << std::left
			 << std::setw(max_resol)
			 << itor->resolved_name
			 << std::string(overhead, ' ')
			 << std::left
			 << std::setw(max_type)
			 << itor->type
			 << std::endl;
	}
	stream << std::string(max_reg + max_resol + max_type + overhead + blanks+3, '#') << std::endl;
  }

  /**
   * @brief Dump the Select Variables to any stream
   *
   * @param stream The stream to pipe the data to. Standard: std::cout
   */
  void print_select_variables (std::ostream & stream = std::cout){
	std::vector<FreeVariables>::const_iterator itor;
	size_t max_len = 0;
	size_t const overheader = 10;
	size_t const blanks = 2;

	std::string const header = "select variables";
	for(itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
	  if (itor->resolved_name.size() > max_len){
		max_len = itor->resolved_name.size();
	  }
	}

	stream << std::string(max_len+overheader+blanks, '#') << std::endl;
	stream << std::string((max_len + overheader - header.size())/2, '#') << " " <<  header;
	stream << " " << std::string((max_len + overheader - header.size())/2,'#') << std::endl;

	for(itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
	  stream << itor->resolved_name << std::endl;
	}
	stream << std::string(max_len+overheader+blanks, '#') << std::endl;
  }

  /**
   * @param Write the smt2 file to the disk
   *
   * @param file The path of the file to create
   */
  void export_smt2(std::string const & file){
	std::string __file = file;
	for(size_t i = 0; i < p_assertions_ordered.size(); ++i){
	  __file = p_root_dir + "/path_" + std::to_string(i) + "_" + file;
	  std::fstream out_file;
	  out_file.open(__file, std::ios::out);
	  std::stringstream sstream;
	  this->write_header(sstream);
	  this->write_variables(sstream);
	  this->write_assertions(sstream,i);
	  this->write_end(sstream);
	  out_file << sstream.str();
	  out_file.close();
#ifdef DEBUG
	  std::cout << "Exported Path " << i << " to " << __file << std::endl;
#endif
	}
  }

private:
  /**
   *  @brief Don't allow CCTOR
   */
  DatabaseExporter (DatabaseExporter & de);

  /*
   * @brief Don't allow assignment operator
   */
  DatabaseExporter& operator= (DatabaseExporter & de);

  /**
   *  @brief Used as indicator for active SQL transactions to switch between the target data structure
   */
  enum active_transition {
	free_variables,
	init,
	assertions
  };

  /**
   * @brief Represent a database entry for a free variable
   */
  struct FreeVariables {
	std::string reg_name;
	std::string resolved_name;
	std::string type;
	bool used;
	
	bool operator== (FreeVariables const & fv){
	  return  !resolved_name.compare(fv.resolved_name);
	}
  };

  struct ReplaceMap{
	std::string key;
	std::string value;
	bool used;

	void dump () {
	  std::cout << "Key: " << key << " Value: " << value << " Used: " << std::boolalpha << used << std::endl;
	}
  };
   
  sqlite3 * p_db;
  std::string p_path;
  active_transition p_active_transition;
  std::vector<FreeVariables> p_free_variables;
  std::vector<FreeVariables> p_select_variables;
  std::vector<std::string> p_assertions;
  std::string p_root_dir;
  size_t p_num_of_problems;
  std::vector<std::vector<std::string> > p_assertions_ordered;

  /**
   * @brief Dummy function for database transactions
   *
   * @param query The SQL query to execute as std::string
   */
  void execute_database_call (std::string query) {
#ifdef DEBUG
	std::cout << "Executing Database Query: " << query << std::endl;
#endif
	int success = -1;

	try {
	  if((success = sqlite3_exec(p_db, query.c_str(), c_callback, this, NULL)) != 0){
		std::string msg = "Can not execute the following QUERY:\n" + query;
		throw new std::runtime_error(msg);
	  }
	} catch (std::runtime_error & err){
	  std::cerr<< err.what() << std::endl;
	}
  }

  /**
   * @brief Static callback function for the sqlite3 api
   * This static function gets the this pointer of the class and forwards the
   * data to an actual member of the class to have access to the memory
   */
  static int c_callback(void *data, int argc, char **argv, char **azColName){
	DatabaseExporter * tmp = reinterpret_cast<DatabaseExporter*>(data);
	return tmp->__callback__(argc, argv, azColName);
  }

  /**
   * @brief Get the free variables from the sqlite database
   */
  void get_free_variables (){
	std::string const query = "SELECT name, position, type FROM free_variables";
	p_active_transition = free_variables;
	execute_database_call(query);
	p_active_transition = init;
	this->extract_select_variables();
	std::vector<FreeVariables> new_variables;
	
	 if(!p_free_variables.empty()) {
		int num_of_assertions = p_assertions_ordered.front().size();
		for(int i = 0 ;i < num_of_assertions; ++i){
		  for(int j = 0; j < p_free_variables.size(); ++j){
			std::string name = p_free_variables[j].resolved_name;
			std::string type = p_free_variables[j].type;
			std::string type_string = resolve_type(type);
			
			FreeVariables tmp;
			tmp.used = false;
			tmp.type = type;
			tmp.reg_name = name;
			tmp.resolved_name = std::string(name + "_" +  std::to_string(i) + std::to_string(j));
			new_variables.push_back(tmp);
		  }
		}
		p_free_variables.clear();
		std::copy(new_variables.begin(), new_variables.end(), std::back_inserter(p_free_variables));
	  }
  }

  /**
   * @brief Extract the select variables out of the free variables
   */
  void extract_select_variables(){
#ifdef DEBUG
	std::cout << "Extract Select Variables..." << std::endl;
#endif
	std::string select = "select_enable";
	std::vector<FreeVariables>::iterator itor;
	for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  if(itor->resolved_name.find(select) != std::string::npos){
		FreeVariables tmp;
		tmp.used = false;
		tmp.resolved_name = itor->resolved_name;
		tmp.reg_name = itor->reg_name;
		tmp.type = itor->type;
		p_select_variables.push_back(tmp);
		p_free_variables.erase(itor);
	  }
	}
  }

  /**
   * @brief Get all model assertions from the database
   *
   * Remember: Each assertions represents one path in the code
   *           even when multiple use cases have been performed
   */
  void get_model_assertions (){
	std::string const query = "SELECT smt FROM models ORDER BY smt;";
	p_active_transition = assertions;
	execute_database_call(query);
	p_active_transition = init;

	std::fstream infile;
	infile.open("/tmp/smt/__num_of_problems__", std::ios::in);
	infile >> p_num_of_problems;
	infile.close();
	boost::filesystem::remove("/tmp/smt/__num_of_problems__");
	int current_problem = 0;
	int chunks = p_assertions.size() / p_num_of_problems;
	for(int i = 0; i < p_num_of_problems; ++i){
	  int cnt = i;
	  std::vector<std::string> tmp(p_assertions.begin()+(cnt*chunks), p_assertions.begin()+((cnt+1)*chunks));
	  p_assertions_ordered.push_back(tmp);
	}
  }

  /*
   * @brief Write the Header/Options to the smt2 stream
   *
   * @param stream The stringstream to write to
   */
  void write_header(std::stringstream & stream){
	std::string header_options = "(set-option :produce-models true)";
	stream << header_options << std::endl;
  }

  /**
   * @brief Write Free Variables to smt2 stream
   *
   * @param stream The stringstream to write to
   */
  void write_variables(std::stringstream & stream){
	try {
	  stream << "; Start Variables" << std::endl;
	  if(!p_select_variables.empty()){
		for(auto itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
		  std::string name = itor->resolved_name;
		  std::string type = itor->type;
		  std::string type_string = resolve_type(type);

		  stream << "(declare-fun " <<  name  << " ()  " << type_string << ")" << std::endl;
		}
	  }

	  if(!p_free_variables.empty()) {
		for(auto itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
		  std::string name = itor->resolved_name;
		  std::string type = itor->type;
		  std::string type_string = resolve_type(type);
		  stream << "(declare-fun " <<  name << " ()  " << type_string << ")" << std::endl;
		  }
		}
	} catch (std::runtime_error & msg){
	  std::cerr << msg.what() << std::endl;
	}
  }

  /**
   * @brief Write all Assertions to the smt2 stream
   *
   * @param stream The stringstream to write to
   */
  void write_assertions(std::stringstream & stream, int path){
	try {
	  if(!p_assertions_ordered.empty()){
		stream << "; Start Assertions" << std::endl;
	
		// #1 Write the assertions gained from the database
		std::vector<std::string> current_stream = p_assertions_ordered[path];
		std::cout << current_stream.size() << std::endl;

		for(std::vector<std::string>::iterator itor = current_stream.begin(); itor != current_stream.end(); ++itor){
		  std::string tmp_string  = itor->substr(0, itor->size()-1);

		  // We need to replace the value name in the assertions
		  std::string values_replaced = update_value_name(tmp_string);
		  // stream << "(assert " << tmp_string << ")" << std::endl;
		  stream << "(assert " << values_replaced << ")" << std::endl;
		}

		for(auto itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
		  itor->used = false;
		}

		// #2 Introduce the soft assertions for the select variables
		//std::vector<std::string>::const_iterator itor;
		//for (itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
		//	stream << "(assert-soft (not " << *itor << "))" << std::endl;
		//}

		// #3 Minimize the number of maximum activated select variables by number
		std::vector<FreeVariables> tmp;
		std::back_insert_iterator< std::vector<FreeVariables> > back_it (tmp);
		std::copy(p_select_variables.begin(), p_select_variables.end(),back_it);
		std::string minimum_assertion = this->minimize_select_variables(tmp, 1);
		stream << minimum_assertion << std::endl;
	  }
	} catch (...){
	  std::cerr << "Unknown Exeception Caught!" << std::endl;
	}
  }

  /**
   * @brief Write the end of the smt2 file to the stream
   *
   * @param stream The stringstream to write to
   */
  void write_end(std::stringstream & stream){
	stream << "; Start Ending" << std::endl;

	// 1. Check SAT
	std::string const check = "(check-sat)";
	stream << check << std::endl;

	// 2. Get Values of all free variables
	for(auto itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
		stream << "(get-value (" << itor->resolved_name << "))" << std::endl;
	}
  }

  /**
   * @brief Recursive function to be called by mimimize_select_variables
   * @param conditions All conditions which have not been used already as vector
   * @param assertion The build assertion as reference type to be build by recursive calls of the function
   *
   * @return void
   */
  void minimize_select_variables_recursion(std::vector<FreeVariables> conditions, std::string & assertion){
	if(!conditions.empty()){
	  assertion += "(ite " + conditions.front().resolved_name + " 1 0)";
	  conditions.erase(conditions.begin());
	  if(!conditions.empty()){
		minimize_select_variables_recursion(conditions, assertion);
	  }
	}
  }

  /**
   * @brief Build an assertion which only allows a certain number of select variables to be enabled by Z3
   * @param conditions All used If-Then-Else conditions as a unique vector
   * @param max_activated_sel_vars Number of select variables which are allowed to be activated in total
   *
   * @return Assertion in SMT2 format to be used in the textual representation
   */
  std::string minimize_select_variables (std::vector<FreeVariables> conditions, size_t const max_activated_sel_vars){
	std::string assertion = "(assert (<= (+ ";
	minimize_select_variables_recursion(conditions, assertion);
	assertion += ") " + std::to_string(max_activated_sel_vars) + " ))";
	return assertion;
  }

  /**
   * @brief Transform a LLVM Datatype to a SMT2 Datatype
   * @param type The type to transform
   * @return The transformed value
   */
  std::string resolve_type(std::string const & type){
	try {
	  if (type == "IntegerTyID32"){
		return "(_ BitVec 32)";
	  } else if (type == "IntegerTyID1"){
		return "Bool";
	  } else {
		throw new std::runtime_error("Datatype not supported yet!");
	  }
	} catch (std::exception const & ex){
	  std::cerr << ex.what() << std::endl;
	}
  }

  /*
   *@brief Update the name of the select_value variables in the assertions
   */
  std::string update_value_name(std::string const & assertion){
	std::string current_input = assertion;
	int cnt = 0;
	
	for(auto itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  if(current_input.find(itor->reg_name) != std::string::npos && itor->used == false){
		std::cout << "Input: " << current_input << std::endl;
		std::cout << "Found Key: " << itor->reg_name << std::endl;
		std::cout << "Replace with: " << itor->resolved_name << std::endl;
		cnt++;
		std::string input = current_input;
		std::string key = itor->reg_name;
		std::string replace_with = " " + itor->resolved_name + " ";
		std::string regex_pattern = " " + key + " ";
		std::regex reg(regex_pattern);
		current_input = std::regex_replace(input, reg, replace_with);
		itor->used = true;
		if(cnt == p_select_variables.size()){
		  break;
		}
	  }
	}
	std::cout << "Output: " << current_input << std::endl;
	return current_input;
  }
};

#endif /* DATABASEEXPORTER_HPP_ */
