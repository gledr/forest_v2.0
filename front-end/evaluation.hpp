#ifndef EVALUATION_HPP_
#define EVALUATION_HPP_

#include <boost/process.hpp>
#include <boost/filesystem.hpp>
#include <iostream>
#include <vector>
#include <regex>

class Evaluation {
public:
	Evaluation (std::string const & directory){
		p_directory = directory;
	}

	~Evaluation () {

	}

	void compile_binary () {

		if (p_source_files.empty()){
			read_directory();
		}

		if (!p_source_files.empty()){
			// Copy file to tmp folder
			boost::filesystem::copy_file(p_source_files.front().path + p_source_files.front().name, "/tmp/smt/"
					+ p_source_files.front().name, boost::filesystem::copy_option::overwrite_if_exists);

			std::string llvm_path = "/usr/src/llvm-3.7/Debug+Asserts/bin/";
			std::string clang = llvm_path;
			if (p_source_files.front().type == SourceFile::eType::c){
				clang += "clang";
			} else {
				clang += "clang++";
			}
			std::string opt = llvm_path + "opt";
			std::string debug_pass = "/usr/src/llvm-3.7/Debug+Asserts/lib/ForestDebug.so";

			boost::process::ipstream is; //reading pipe-stream
			std::string cmd = " -c -emit-llvm /tmp/smt/" + p_source_files.front().name + " -o /tmp/smt/file.bc";
			boost::process::child c1(clang +  cmd, boost::process::std_out > is);

			std::string line;
			while (c1.running() && std::getline(is, line) && !line.empty()){
				std::cerr << line << std::endl;
			}
			c1.wait();

			cmd.clear();
			line.clear();

			cmd = " -load " + debug_pass +
			      " -loop_latch_info -insert_select_variables " +
				  "/tmp/smt/file.bc -o /tmp/smt/file2.bc";
			boost::process::ipstream is2; //reading pipe-stream
			boost::process::child c2(opt +  cmd, boost::process::std_out > is2);

			while (c2.running() && std::getline(is2, line) && !line.empty()){
				std::cerr << line << std::endl;
			}
			c2.wait();

			cmd.clear();
			line.clear();

			cmd = " -load " + debug_pass +
			      " -inject_results " +
				  "/tmp/smt/file2.bc -o /tmp/smt/file3.bc";
			boost::process::ipstream is3; //reading pipe-stream
			boost::process::child c3(opt +  cmd, boost::process::std_out > is3);

			while (c3.running() && std::getline(is3, line) && !line.empty()){
				std::cerr << line << std::endl;
			}
			c3.wait();

			cmd.clear();
			line.clear();

			cmd = " -std=c++11 /tmp/smt/file3.bc /home/sebastian/forest_fork/forest_v2.0/lib/libeval.a -lsqlite3 -o /tmp/smt/EvalBin";
			boost::process::ipstream is4; //reading pipe-stream
			boost::process::child c4(llvm_path + "clang++" +  cmd, boost::process::std_out > is4);

			while (c4.running() && std::getline(is4, line) && !line.empty()){
				std::cerr << line << std::endl;
			}
			c4.wait();

		}

	}

	std::string get_directory () const {
		return p_directory;
	}

private:
	// Make Canonical Class
	Evaluation (Evaluation const & eval);
	Evaluation operator= (Evaluation const & eval);
	bool operator== (Evaluation const & eval);

	class SourceFile {
	public:
		enum eType {cpp, c};
		std::string path;
		std::string name;
		eType type;
	};

	std::string p_directory;
	std::vector<SourceFile> p_source_files;



	void read_directory(){
		try {
			std::vector<std::pair<std::string, std::string> > found_files;
			boost::filesystem::path dir(p_directory);

			if (boost::filesystem::is_directory(p_directory)){
				boost::filesystem::directory_iterator itor(p_directory);

				for(; itor != boost::filesystem::directory_iterator(); ++itor){
					if (boost::filesystem::is_regular_file(itor->status())){
						std::pair<std::string, std::string> tmp;
						size_t slash = 0;
						std::string current_file = itor->path().string();
						for(int i = current_file.size(); i >= 0; --i){
							if(current_file[i] == '/'){
								slash = i;
								break;
							}
						}
						tmp.first = itor->path().string().substr(0, slash+1);
						tmp.second = itor->path().filename().string();
						found_files.push_back(tmp);
					}
				}
			} else {
				std::string msg = p_directory + " is no valid directory!";
				throw std::runtime_error(msg);
			}

			if (!found_files.empty()){
				std::regex c_files ("([\\w+]+).c");
				std::regex cpp_files ("([\\w+]+).cpp");
				for(auto itor = found_files.begin(); itor != found_files.end(); ++itor){
					if (std::regex_match(itor->second, c_files)){
						SourceFile tmp;
						tmp.path = itor->first;
						tmp.name = itor->second;
						tmp.type = SourceFile::eType::c;
						p_source_files.push_back(tmp);
					}
					else if (std::regex_match(itor->second, cpp_files)){
						SourceFile tmp;
						tmp.path = itor->first;
						tmp.name = itor->second;
						tmp.type = SourceFile::eType::cpp;
						p_source_files.push_back(tmp);
					}
				}
			}
		} catch (std::runtime_error & msg){
			std::cerr << msg.what() << std::endl;
		}
	}

};



#endif /* EVALUATION_HPP_ */
