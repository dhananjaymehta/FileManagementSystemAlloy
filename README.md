# FileManagementSystemAlloy

O V E R V I E W:
------------------

Kansas Federal University requires system in place that allows the users i.e. faculty and students as they may work on a file across multiple devices i.e. notebook or desktop computers around a clock to synchronize contents of files. The users can work with these devices across any location i.e. at home, in their office, or while traveling. In order to make this possible KSU needs a File Management System(FMS)that will synchronize contents of the various file systems. This allows the users to work on one device, and then propagate the changes to other devices.


SPECIFIC   REQUIREMENTS:
-------------------------------------------
1. Create FMS for Kansas State University to manage the files of its "Students" and "Faculty".
2. System will have two users - Faculty & Students.
3. Each user of FMS shall be registered, which means user should be part of KSU. A non registered user cannot access the FMS.
4. A user can work on multiple devices - Desktop Computer, Notebook.
5. User shall be able to access a file it owns from across all devices user owns.
6. FMS shall maintain a table of files owned by user.
7. FMS shall maintain a table of devices owned by the user.
8. FMS allows a user  to access a file from his registered devices from any locations - Office, Home, or Traveling. User can be physically present at one of the above locations at a time.
9. FMS should synchronize content of files so that any change made to a file from any of the registered devices is reflected across all other devices of the user when user access these files.
10. Files in FMS are organized in a hierarchical tree structure where files are placed inside a directory or subdirectory. 
11. Files have been be categorized as - Normal and Sensitive. Sensitive files are the ones which have certain restrictions on them. Example: File containing student's data shall only be on Desktop and not Notebook.
12. System should be able to take a backup of all files , this allows user to restore files in case of any mistake or error.


SYSTEM   CONSTRAINTS:
--------------------------------------
1. A file when accessed by a user can have one of two status -  Read or Write at a time. A file can not have two status simultaneously.
2. A file can be located under only one directory and subdirectory , it should not be present at two separate directories as file path is always unique.
3. Once the file changes FMS should recognize changes in the file. A change in file can be detected when status of files changes from Read -> Write or Write-> Read. These changes in file status can be maintained by a log file. 
4. A file in READ status can be accessed by any registered user who has access to the file. Access table is created to maintain an entry of user who can access a file. 
5. A file in WRITE status can be accessed by only one user and from only one device. This is to avoid multiple write to a file in FMS. This check avoids to place additional check to test multiple updates on a file.
6. Backups are stored in a separate directory and not inside directory where files are stored. This helps if entire filesystem fails on FMS.
7. FMS shall automatically take backup. To allow automatic backup, files are backed up when status of a file changes from Write to Read.
8. Files are automatically synchronized when status of file changes from Write to Read.
9. User is able to access a file from multiple locations.




