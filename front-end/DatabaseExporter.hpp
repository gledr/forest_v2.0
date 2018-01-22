#ifndef DATABASEEXPORTER_HPP_
#define DATABASEEXPORTER_HPP_

#include <iostream>
#include <iomanip>
#include <string>
#include <sqlite3.h>
#include <boost/filesystem.hpp>
#include <vector>
#include <set>

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
		try{
			if (boost::filesystem::exists(dir)){
#ifdef DEBUG
				std::cout << "Removing directory " << dir << "..." << std::endl;
#endif
				if(boost::filesystem::remove_all(dir) == 0){
					std::string msg = "Could not remove directory: " + dir;
					throw std::runtime_error(msg);
				}
			}
#ifdef DEBUG
			std::cout << "Creating directory " << dir << "..." << std::endl;
#endif
			if(boost::filesystem::create_directories(dir) == false){
				std::string msg = "Could not create directory " + dir;
				throw std::runtime_error(msg);
			}
		} catch (std::runtime_error & msg){
			std::cerr << msg.what() << std::endl;
		}
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
		this->get_free_variables();
		this->extract_select_variables();
		this->get_model_assertions();
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

				if(std::find(p_free_variables.begin(), p_free_variables.end(), table_entry) == p_free_variables.end()){
					p_free_variables.push_back(table_entry);
					std::cout << "inserting " << table_entry.resolved_name << std::endl;

				}
			} else if (p_active_transition == assertions){
				assert (argc == 1);
				p_assertion_paths.push_back(argv[0]);
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
		std::vector<std::string>::const_iterator itor;
		size_t max_len = 0;
		size_t const overheader = 10;
		size_t const blanks = 2;

		std::string const header = "select variables";
		for(itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
			if (itor->size() > max_len){
				max_len = itor->size();
			}
		}

		stream << std::string(max_len+overheader+blanks, '#') << std::endl;
		stream << std::string((max_len + overheader - header.size())/2, '#') << " " <<  header;
		stream << " " << std::string((max_len + overheader - header.size())/2,'#') << std::endl;

		for(itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
			stream << *itor << std::endl;
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
		for(size_t i = 0; i < p_assertion_paths.size(); ++i){
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

		bool operator== (FreeVariables const & fv){
			return  !resolved_name.compare(fv.resolved_name);
		}
	};


	sqlite3 * p_db;
	std::string p_path;
	active_transition p_active_transition;
	std::vector<FreeVariables> p_free_variables;
	std::vector<std::string> p_select_variables;
	std::vector<std::string> p_assertion_paths;
	std::string p_root_dir;

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
				p_select_variables.push_back(itor->resolved_name);
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
		std::string const query = "SELECT path FROM models";
		p_active_transition = assertions;
		execute_database_call(query);
		p_active_transition = init;
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
			std::vector<FreeVariables>::const_iterator itor;
			for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
				std::string name = itor->resolved_name;
				std::string type = itor->type;
				std::string type_string;

				if (type == "IntegerTyID32"){
					type_string = "(_ BitVec 32)";
				} else if (type == "IntegerTyID1"){
					type_string = "bool";
				} else {
					throw new std::runtime_error("Datatype not supported yet!");
				}

				stream << "(declare-const " << name << " " << type_string << ")" << std::endl;
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
			if(!p_assertion_paths.empty()){
				stream << "; Start Assertions" << std::endl;

				// #1 Write the assertions gained from the database
				std::string current_stream = p_assertion_paths[path];
				std::vector<std::string> elems = this->split(current_stream, ",");

				for(std::vector<std::string>::const_iterator itor = elems.begin(); itor != elems.end(); ++itor){
					stream << "(assert " << *itor << ")" << std::endl;
				}

				// #2 Introduce the soft assertions for the select variables
				std::vector<std::string>::const_iterator itor;
				for (itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
					stream << "(assert-soft (not " << *itor << "))" << std::endl;
				}

				// #3 Minimize the number of maximum activated select variables by number
				std::vector<std::string> tmp;
				 std::back_insert_iterator< std::vector<std::string> > back_it (tmp);
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
		std::vector<FreeVariables>::const_iterator itor;
		std::string keyword_select = "select";
		for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
			if(itor->resolved_name.find(keyword_select) != std::string::npos)
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
	void minimize_select_variables_recursion(std::vector<std::string> conditions, std::string & assertion){
		if(!conditions.empty()){
			assertion += "(ite " + conditions.front() + " 1 0)";
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
	std::string minimize_select_variables (std::vector<std::string> conditions, size_t const max_activated_sel_vars){
		std::string assertion = "(assert (<= (+ ";
		minimize_select_variables_recursion(conditions, assertion);
		assertion += ") " + std::to_string(max_activated_sel_vars) + " ))";
		return assertion;
	}

	/**
	 * @brief Split a string at delimiter and pack them into a vector
	 *
	 * @param str The string to split
	 * @param delim The delimiter to use
	 */
	std::vector<std::string> split(std::string const & str, std::string const & delim) {
	    std::vector<std::string> tokens;
	    size_t prev = 0;
	    size_t pos = 0;

	    do
	    {
	        pos = str.find(delim, prev);
	        if (pos == std::string::npos) pos = str.length();
	        std::string token = str.substr(prev, pos-prev);
	        if (!token.empty()) tokens.push_back(token);
	        prev = pos + delim.length();
	    }
	    while (pos < str.length() && prev < str.length());

	    return tokens;
	}
};

#endif /* DATABASEEXPORTER_HPP_ */
