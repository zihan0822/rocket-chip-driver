#include <fesvr/dtm.h>
#include <iostream>
#include <rocket_chip_driver.h>


int main(int argc, char* argv[]) {
   if (argc < 2) {
      std::cerr << "Expect btor file" << std::endl;
      return 1;
   }
   char* btor_file_path = argv[1];
   ffi::bootstrap_driver(btor_file_path);
   ffi::step_driver();
   return 0; 
}