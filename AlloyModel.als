/* 
CIS771 - Extra Credit 
Dhananjay Mehta and Shubh Chopra
F I L E    M A N A G E M E N T   S Y S T E M
-- This model include the Alloy model for FMS and also include the test to check the implementation.
*/ 

//==============================================
// F I L E    M A N A G E M E N T   S Y S T E M : Basic Framework
//==============================================

--Users of FMS
abstract sig  User {}

--Two kind of users 
sig student, faculty extends User{}

--Devices registered to FMS
abstract sig Devices {}

--Two kind of devices
sig Laptop, Desktop extends Devices{}

--Location where the devices can be located.
sig Location
{
associatedDevice: some Devices
}

--FSM consists of a Diretory Tree having subdirectories and Files
sig Directory {}

-- A File has a Status and Permissions associated with it
sig File{
permission: one Permission
}

-- Indicates status of a File
abstract sig Status{}
one sig Read,Write extends Status{}

-- Indicates permissions on a File.
abstract sig Permission{}
one sig Personal,Sensitive extends Permission{}

// Backup files in FMS.
one sig Backup {}


//==============================================
// F I L E    M A N A G E M E N T   S Y S T E M : Definition 
//==============================================

sig FMS 
{
// FSM saves a set of Active users
registereduser : set User,

//logfile saves status of a file READ/WRITE in FSM.
logfile: File -> one Status,

//FSM keep tracks location where user is located and set the location as active location.
activelocation : set Location,

//File directory indicate the directory of the file in FMS.
filedirectory: File -> one Directory ,

//subdirectory give information about the sub directories of a Directories in FMS.
subdirectory: Directory -> lone Directory,

//ownertable indicates owner of a file in FMS.
ownertable: File ->one User,

//accesstable indicates people who can access the file in FMS.
accesstable: User-> File,

//devicetable indicates device on which file is located in FMS.
devicetable: Devices -> File,

//deviceuser indicates device a user owns that are associated to FMS.
deviceuser: Devices some -> one User,

//backupfiles backs up file in FMS.
backupfiles: File -> lone Backup,
}

//====================================
// F I L E    M A N A G E M E N T   S Y S T E M : Signature Facts 
//====================================

{
//all the users who can access a file should be a registered user
all u:User| (u in File.ownertable) implies u in registereduser

// if a file is accessble by a user and is Private then it is accessed by only the owner in all its devices
all f:File | f.permission = Personal implies  f.ownertable in accesstable.f  and f in (deviceuser.(f.ownertable)).devicetable 

// if a file is accessble by a user and is Sensitive then it is acessed by only owner and only through desktop
all f:File |(f in User.accesstable) and f.permission in Sensitive implies  f.ownertable  in accesstable.f 
and devicetable.f in Desktop 

//unregistered user has no devices
all u:User|(u & registereduser = none) implies deviceuser.u = none

//a subdirectory can not be its own directory
all f1,f2:Directory|(f1.subdirectory=f2) implies f2.subdirectory!=f1

//no transitive closure of subdirectories
no d: Directory | d in d.^subdirectory

// there is only one directory and all files are saved in the directory
all f:File | (f.logfile = Read) implies f in backupfiles.Backup

//backup has no file currently written
all f:File | (f.logfile = Write) implies f not in backupfiles.Backup

//Every owner has access to its file
all f:File , u:User| (u in f.(ownertable)) implies u in (accesstable).f and #(accesstable).f >=1

//Every file has to be in at least one device
all f: File | #(devicetable.f) >= 	1

//Only owner can write the file and when the file is writing no one else can access it and only on one device
all f:File| (f.logfile=Write) implies accesstable.f in f.ownertable and #(devicetable.f) = 1

//if the file have a Status read then it has to be in at least all the devices of the owener
all f:File| (f.logfile=Read) implies deviceuser.(f.ownertable) in devicetable.f 

//all the devices where the file is accesseble should be owned by users having access to the file
all f:File| devicetable.f in deviceuser.(accesstable.f)
}

-- This fact indicates that a device cannot be in more than one location at a given time.
fact devicemultiplelocation
{
all l1,l2:Location | l1.associatedDevice & l2.associatedDevice  = none
}


//======================================
// F I L E    M A N A G E M E N T   S Y S T E M : System Constraints
//======================================

-- 1. FileUpdate
-- When a file switches from Write to Read that means that file has done being updated and cab be published to other devices
-- 
pred FileUpdate (f:File, fms,fms':FMS)
{
//Both file are different
fms'!=fms
//precondition file status should be Write
f.(fms.logfile) = Write
//precondition file should be on one device (owened by the user)  and should be accessed by only one user (owner)
(fms.accesstable).f + f.(fms.ownertable) = f.(fms.ownertable) and #(fms.devicetable.f) =1 and fms'.devicetable.f in fms'.deviceuser.(f.(fms'.ownertable))
//postcondition file status should be Read
f.(fms'.logfile) = Read
//postcondition add file in back up
f in fms'.backupfiles.Backup
//frame conditions 
fms.registereduser = fms'.registereduser
all f1:File-f | f1.(fms.logfile) = f1.(fms'.logfile)
fms.filedirectory = fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
fms.accesstable=fms'.accesstable
fms.devicetable=fms'.devicetable
fms.deviceuser=fms'.deviceuser
(fms'.backupfiles).Backup= (fms.backupfiles).Backup + f
}
run  FileUpdate for 2

-- 2. FileNotUpdate 
-- When a file switches from Read to Write that means that file is being updated and has to be un published (should only hace one user in accesstable and should only be in one device)
-- 
pred FileNotUpdate (f:File, fms,fms':FMS)
{
//Both file are different
fms' != fms
//precondition file status should be Read
f.(fms.logfile) = Read
//postcondition file should be on one device (owened by the user) and should be accessed by only one user (owner)
(fms'.accesstable).f + f.(fms'.ownertable) = f.(fms'.ownertable) and #(fms'.devicetable.f) =1 and fms'.devicetable.f in fms'.deviceuser.(f.(fms'.ownertable))
//postcondition file status should be Read
f.(fms'.logfile) = Write
//postcondition remove file from back up
f not in fms'.backupfiles.Backup
//frame conditions 
fms.registereduser = fms'.registereduser
all f1:File-f | f1.(fms.logfile) = f1.(fms'.logfile)
all f2:File-f | (fms.accesstable).f2=(fms'.accesstable).f2
all f3:File-f | (fms.devicetable).f3=(fms'.devicetable).f3
fms.filedirectory = fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
fms.deviceuser=fms'.deviceuser
(fms.backupfiles).Backup= (fms'.backupfiles).Backup + f
}
run  FileNotUpdate for 2

-- 3. givingaccess
-- Giving access to some other user to access a file.
--
pred givingaccess (u:User, fms,fms':FMS , f:File)
{

//Both file are different
fms'!=fms
//precondition file status should be Read
f.(fms.logfile) = Read
//per condition file should not be accessed by user
u not in (fms.accesstable).f
//postcondition file should be given access to the user
u in (fms'.accesstable).f

//frame conditions 
fms.registereduser = fms'.registereduser
fms.logfile = fms'.logfile
fms.filedirectory = fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
all f1:File-f | (fms.accesstable).f1=(fms'.accesstable).f1
all f2:File-f | (fms.devicetable).f2=(fms'.devicetable).f2
fms.deviceuser=fms'.deviceuser
(fms'.backupfiles).Backup= (fms.backupfiles).Backup
} 
run givingaccess for 2

-- 4. removeaccess
-- Remove Access for a User to  file.
-- 
pred removeaccess (u:User, fms,fms':FMS , f:File)
{
//Both file are different
fms'!=fms
//precondiotion user can not be the owner of the file
u != f.(fms.ownertable)
//precondition file status should be Read because the other user has the rights to just read the file not write it
f.(fms.logfile) = Read
//precondition file should be given access to the user
u in (fms.accesstable).f
//postcondition file should not be accessed by user
u not in (fms'.accesstable).f
//postcondition file should not be in any device of that user
f not in ((fms.deviceuser).u).(fms'.devicetable)
//frame conditions 
fms.registereduser = fms'.registereduser
fms.logfile = fms'.logfile
fms.filedirectory = fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
all f1:File-f | (fms.accesstable).f1=(fms'.accesstable).f1
all f2:File-f | (fms.devicetable).f2=(fms'.devicetable).f2
fms.deviceuser=fms'.deviceuser
(fms'.backupfiles).Backup= (fms.backupfiles).Backup
}
run removeaccess for 2

-- 5. addFiletoDevice
--	Change location of the device(only laptop)
--
pred addFiletoDevice (f:File ,fms,fms':FMS, d:Devices)
{
//Both file are different
fms'!=fms
//percondition file not in that device
f not in d.(fms.devicetable)
//postcondition file in that device
f in d.(fms'.devicetable)
//frame conditions 
fms.registereduser = fms'.registereduser
fms.logfile = fms'.logfile
fms.filedirectory= fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
all f1:File-f | (fms.accesstable).f1=(fms'.accesstable).f1
all f2:File-f | (fms.devicetable).f2=(fms'.devicetable).f2
all d1:Devices-d | d1.(fms.deviceuser)=d1.(fms'.deviceuser)
(fms'.backupfiles).Backup= (fms.backupfiles).Backup
}
run addFiletoDevice for 2

--
-- 6. Remove a file to Device
-- 
pred removeFiletoDevice (f:File ,fms,fms':FMS, d:Devices)
{
//Both file are different
fms'!=fms
//precondition file in that device
f in d.(fms.devicetable)
//postcondition file not in that device
f not in d.(fms'.devicetable)
//frame conditions 
fms.registereduser = fms'.registereduser
fms.logfile = fms'.logfile
fms.filedirectory= fms'.filedirectory
fms.activelocation = fms'.activelocation
fms.subdirectory=fms'.subdirectory
fms.ownertable= fms'.ownertable
all f1:File-f | (fms.accesstable).f1=(fms'.accesstable).f1
all f2:File-f | (fms.devicetable).f2=(fms'.devicetable).f2
all d1:Devices-d | d1.(fms.deviceuser)=d1.(fms'.deviceuser)
(fms'.backupfiles).Backup= (fms.backupfiles).Backup
}
run removeFiletoDevice for 2


//==============================================
// F I L E    M A N A G E M E N T   S Y S T E M : Debugging/ Testing
//==============================================

-- 1. RegisteredUserAccess
-- This assestion shows a file can only be accessed(read/write) by a registered user.
-- 
assert RegisteredUserAccess{
all fms:FMS, f: File | fms.ownertable[f] =fms.registereduser
}
check RegisteredUserAccess for 1


-- 2. OwnerWriteAccessFile
-- This assertion shows that only Owner has access to open file in WRITE (i.e. to edit)
--
assert OwnerWriteAccessFile{
all f: File, fms:FMS | fms.logfile[f]=Write implies fms.ownertable[f]  in fms.registereduser
}
check OwnerWriteAccessFile for 1

-- 3. UsersReadAccess
-- This assertion shows that anyone who has access to a file can read a file.
--
assert UsersReadAccess{
all f: File, fms:FMS | fms.logfile[f]=Read implies fms.accesstable.f in fms.registereduser
}
check UsersReadAccess for 1

-- 4. SingleDeviceAccess
-- This assertion shows that a file in Write mode can be accessed from only one Device.
-- 
assert SingleDeviceAccess{
all f:File, fms:FMS | fms.logfile[f]=Write implies #(fms.devicetable.f) =1
}
check SingleDeviceAccess for 1

-- 5. MultipleDeviceAccess
-- This assertion checks if multiple devices can access a file in read mode.
-- 
assert MultipleDeviceAccess{
all f:File, fms: FMS | fms.logfile[f] = Read implies #(fms.devicetable.f) >=0
}
check MultipleDeviceAccess for 1

-- 6. CheckFileStatus
-- This assertion checks that file has atleast one status - READ or WRITE
-- 
assert CheckFileStatus{
all f: File, fms: FMS | fms.logfile[f]=Read or fms.logfile[f]=Write
}
check CheckFileStatus for 1

-- 7. CheckIfFileInDirectory
-- This assertion checks that a file is inside a directory and maintains a hierarchial structure.
--
assert CheckIfFileInDirectory{
all f:File, fms: FMS | #(fms.filedirectory[f]) = 1
}
check CheckIfFileInDirectory for 1

-- 8. CheckSensitiveFile
-- This assertion checks that a sensitive file resides only on Desktop.
-- 
assert CheckSensitiveFile{
all f:File,fms:FMS | f.permission=Sensitive implies fms.devicetable.f = Desktop
}
check CheckSensitiveFile for 1

-- 9. CheckPersonalFile
-- This assertion checks that a personal or a non-sensitive file can reside on any device.
-- 
assert CheckPersonalFile{
all f:File,fms:FMS | f.permission=Personal implies fms.devicetable.f = Desktop or  fms.devicetable.f = Laptop
}
check CheckPersonalFile for 1

-- 10. CheckForBackup
-- This assertion checks that a file is backed up when a file is updated.
-- 
assert CheckForBackup{
all f:File, fms,fms':FMS | FileUpdate[f, fms,fms'] implies
#((fms'.backupfiles).Backup)= #((fms.backupfiles).Backup + 1)
}
check CheckForBackup for 1

--11. BackupUpdated
--This assertion checks that if all the files in Read mode are backed up or not
assert BackupUpdated{
all f:File,fms:FMS | fms.logfile[f] = Read implies f in (fms.backupfiles).Backup 
}

check BackupUpdated for 1
