module androidPermisison

/**
	* A model of the Android Runtime Permission Protocol
	*
	* Author: Guliz Seray Tuncay
	*
	* Adopted from: http://groups.csail.mit.edu/sdg/projects/android/
	*/

open util/relation as rel
open util/ordering[Time] as to
open util/integer as integer
open util/natural as nat
open util/boolean as boolean

sig Time {}
abstract sig Name {}
sig PackageName, PermName, PermGroupName extends Name {}
sig AppSignature {}

abstract sig Permission { 
	name: PermName,  
	protectionLevel: ProtectionLevel, 
	sourcePackage : PackageName,
	isCustomPermission: Bool,
	permGroup: lone PermGroupName,
	sourceId: AppSignature
}

sig PermissionGroup {
	name: PermGroupName,
	perms: Permission -> Time
}

// To protect app components
sig Guard {
	name: PermName,
}

abstract sig ProtectionLevel {}
one sig Normal, Dangerous, Signature extends ProtectionLevel {} 

one sig ModelTracking {
	isUserPromptScreenShown: Bool -> Time
}

one sig Device {
	apps: Application -> Time,
	builtinPerms : set Permission, // system permissions
	// custom permissions that are currently active on the device
	customPerms: Permission -> Time,
	platformPackageName: one PackageName,
	platformSignature : one AppSignature,
	builtinPermGroups: set PermissionGroup
}{
	all t: Time | customPerms.t in (apps.t).declaredPerms.t

	// Two apps on device cannot have the same (package) name
	all t: Time,  disj app1, app2: Application | 
		app1 in apps.t and app2 in apps.t implies app1.packageName != app2.packageName

	// No two permissions with the same name
	all t: Time,  disj p1, p2: Permission | 
		(p1 + p2) in (builtinPerms + customPerms.t) implies p1.name != p2.name

	// all builtin permissions will have "android" as their source package
	all p: builtinPerms | p.sourcePackage = platformPackageName

	// all builtin permissions will have the platform signature as their source id
	all p: builtinPerms | p.sourceId = platformSignature

	// all builtin permissions will NOT be customPermissions
	all p: builtinPerms | p.isCustomPermission = False

	// all permissions in permissions groups must exist on the device
	all t: Time, p: Permission |
		p in builtinPermGroups.perms.t implies p in builtinPerms + customPerms.t

	// if a permission is in a permission group, its permission group name should
	// be th same as the name of that group. 
	// This way we also cannot have a permission exist in two groups
	// or a permission w/ no name in permission groups.
	all t: Time, pg: builtinPermGroups, p: Permission |
		p in pg.perms.t implies p.permGroup = pg.name

	// all permission groups have unique names
	all disj pg1, pg2: PermissionGroup |
		(pg1 + pg2) in builtinPermGroups implies pg1.name != pg2.name
}


run traces for 9
check NoUnauthorizedAccess for 7 but exactly 7 Time, 3 Application, 2 Permission, 2 Component, 1 PermissionData, 6 Int

sig Application {
	packageName : PackageName,
	signature : one AppSignature,
    // set of permissions that the app declares in the app manifest 
	// (also called custom permissions)
	declaredPerms: Permission -> Time,
    // set of permissions that the app uses. It is modeled after the 
	// <uses-permission> tag in the app manifest
	// http://developer.android.com/guide/topics/manifest/uses-permission-element.html
	usesPerms: PermName -> Time,
	// permission that other apps need to have to interact with this app
	guard : lone Guard,
	components: set Component,
	targetSDK : Int -> Time, // for ints, the range is according to number of objects in run statement
	// e.g. 'run predicateName for 3' means range for integers is [-2^n, 2^n -1]
	permissionsState: PermissionData -> Time
}{
	all t: Time | 	one targetSDK.t and targetSDK.t > 0 and targetSDK.t <= 26// an app can have a single targetSDK value
	all t: Time - last  | let t' = t.next | targetSDK.t <= targetSDK.t' // you cannot downgrade

	// TODO (gulizseray): guard should be allowed to be ANY permission on the device
	// and not just the permissions defined by this app + builtin permissions
	//all t:Time | guard.name in (declaredPerms.t + Device.builtinPerms).name
	all t:Time | guard.name in (	Device.customPerms.t + Device.builtinPerms).name
	
	// an app cannot define the same permission more than once.
	all t:Time | no disj p1,p2: declaredPerms.t | p1.name = p2.name

	// all permissions declared by an app will have the app's name as their source package
	all t:Time | all p: declaredPerms.t | p.sourcePackage = packageName

	// all permissions declared by an app will have the app's signature as their source id
	all t:Time | all p: declaredPerms.t | p.sourceId = signature

	// permissionsState cannot have two entries for the same permission
	all t: Time, disj pd1, pd2: PermissionData | 
		(pd1 + pd2) in permissionsState.t implies pd1.perm != pd2.perm

	// permissionsState cannot have two entries for the same permission name??
	all t: Time, disj pd1, pd2: PermissionData | 
		(pd1 + pd2) in permissionsState.t implies pd1.perm.name != pd2.perm.name

	// uninstalled apps can never have permission data
	// not sure if absolutely necessary
	all t: Time, pd: PermissionData | this not in Device.apps.t implies pd not in permissionsState.t

	// all custom permissions will be set as custom permissions
	all t: Time, p: declaredPerms.t | p.isCustomPermission = True

	// if package name is "android", then this is a system app and should be signed with platform signature
	// and vice versa
	// TODO (gulizseray): we should be able to relax the naming rule. Currently all system apps 
	// will have the same name; however, this doesn't have any effect on the outcome.
	packageName = Device.platformPackageName implies signature = Device.platformSignature
	signature = Device.platformSignature implies packageName = Device.platformPackageName
}

pred noChangesToAppManifest[app: Application, t, t': Time] {
	app.declaredPerms.t' = app.declaredPerms.t
	app.usesPerms.t' = app.usesPerms.t
	app.targetSDK.t' = app.targetSDK.t
}

sig Flags {
	FLAG_PERMISSION_GRANTED_BY_DEFAULT: Bool,
	FLAG_PERMISSION_SYSTEM_FIXED: Bool,
	FLAG_PERMISSION_REVOKE_ON_UPGRADE: Bool,
	FLAG_PERMISSION_POLICY_FIXED: Bool
}

sig PermissionData {
	perm: one Permission,
	flags: Flags,
	isRuntime: Bool
}

abstract sig Component {
	app: one Application,
	// permission that other apps need to have to access this component
	guard: lone Guard,
	// (c, t) is a tuple in causes if "this" has (directly or indirectly) caused a call to "c" 
	// in the history leading up to "t"
	causes : Component -> Time
}{
	// TODO (gulizseray): shouldn't guard be allowed to be ANY permission on the device
	// and not just the permissions defined by this app + builtin permissions
	//guard.name in (app.declaredPerms.t + Device.builtinPerms).name
	all t: Time | guard.name in (app.declaredPerms.t + Device.builtinPerms).name
	this in app.components
}


fact CausalChain {
	// define what it means for some component ("from") to cause a call to another ("to")
	all from, to : Component, t : Time - last |
		from -> to in causes.t iff {
			// "from" directly invokes "to"
			invoke[t, t.next, from, to] or
			// there's an intermediate component "c'" such that "from" causes c' and "c'" invokes "to"
			(some c' : Component | from -> c' in causes.t and invoke[t, t.next, c', to]) or 
			// "(from, to)" is already in the causal chain in the previous time step
			(t != first and from -> to in causes.(t.prev))
		}
	causes.last = causes.(last.prev)
}

fact Wellformedness {
	// each Component belongs to exactly one Application
	components in Application one -> Component 
	// no custom permissions can be named the same way as a built-in permission
	all t:Time | no p : Application.declaredPerms.t | p.name in Device.builtinPerms.name
	// all predefined permissions have a distinct name
	no disj p1, p2 : Device.builtinPerms | p1.name = p2.name
	// each (PermissionData -> Time) tuple belongs to at most one app
	permissionsState in Application lone -> (PermissionData -> Time)
	
	// only one app can declare one Permission instance (not the name)
	all t:Time | no disj app1, app2 : Application, p: Permission |
		p in app1.declaredPerms.t and p in app2.declaredPerms.t 
	
	// builtin permission cannot be redeclared (cannot refer to same Permission instance)
	all t:Time | no p: Device.builtinPerms, app: Application | p in app.declaredPerms.t
}

abstract sig Activity extends Component {}
abstract sig Service extends Component {}
abstract sig BroadcastReceiver extends Component {}
// ContentProviders look just like other components in this model.
// This is because we exclude URI permissions for content providers.
abstract sig ContentProvider extends Component {}

fact Assumption {
	// can't install an app with the same name as existing one
	all t : Time - last, app : Application |
		install[t, t.next, app] implies
			app.packageName not in (Device.apps.t).packageName
}

fun returnValidPermNames[app : Application, t : Time]: set PermName {
	let perms = returnValidPerms[app, t] {
		{ pname: PermName | pname in perms.name }
	}
}

fun returnValidPerms[app : Application, t : Time] : set Permission {
	{ perm: Device.customPerms.t + Device.builtinPerms |
			perm.name in app.usesPerms.t and
			(perm.protectionLevel = Normal
				or perm.protectionLevel = Dangerous
				or (perm.protectionLevel = Signature
						and 
						(verifySignatureForCustomPermission[perm, app, t] 
							or verifySignatureForBuiltinPermission[perm, app]
						)
					)
			)
	}
}

pred verifySignatureForCustomPermission[perm : Permission, app : Application,  t :  Time] {
	perm not in Device.builtinPerms
	// if permission exists on the device, then check signature. (else return true)
	//perm in Device.customPerms.t =>
	findAppByName[perm.sourcePackage, t].signature = app.signature
}

pred verifySignatureForBuiltinPermission[perm : Permission, app : Application] {
	perm in Device.builtinPerms
	app.signature = Device.platformSignature
}

pred addPermsToBuiltinPermGroupsOld[t, t': Time, pset : set Permission] {
	all p: pset, pg: Device.builtinPermGroups |
		p.permGroup = pg.name implies p in pg.perms.t'
}

pred removePermsToBuiltinPermGroups[t, t': Time, pset : set Permission] {
	all p: pset, pg: Device.builtinPermGroups | p not in pg.perms.t'
}

// pset is the new set of permissions being added to device dng installation
pred addPermsToBuiltinPermGroups[t, t': Time, pset : set Permission] {
	all p: Permission, pg: Device.builtinPermGroups |
		p in pset and p.permGroup = pg.name => p in pg.perms.t'
		else
			// keep existing perm groups intact
			p in pg.perms.t => p in pg.perms.t'
			else
				p not in pg.perms.t'
}

// The app installation is described by this operation:
pred install[t, t' : Time, app : Application] {
	app not in Device.apps.t //precondition
  	Device.apps.t' = Device.apps.t + app
	grantPermissions[app, t, t']
	-- can't install an app with a declared permission that's named the same as existing one
	no p : app.declaredPerms.t | p.name in (Device.customPerms.t).name
	Device.customPerms.t' = Device.customPerms.t + app.declaredPerms.t
	all a : Application - app | a.permissionsState.t' = a.permissionsState.t

	// Adjust permission groups
	all pg: Device.builtinPermGroups, p: Permission |
		p in pg.perms.t or (p in app.declaredPerms.t' and p.permGroup = pg.name)
			=> p in pg.perms.t' else p not in pg.perms.t'
}



// This function returns a set of permissions that are declared in "app"
// and not already active on the device
fun newCustomPerms[t : Time, app : Application] : set Permission {
	{p : app.declaredPerms.t |  p.name not in (Device.customPerms.t).name }
}

// This function returns the currently active permission with name p 
fun findPermissionByName[p : PermName, t : Time] : one Permission {
	(Device.customPerms.t + Device.builtinPerms) & name.p
}

fun findAppByName[a : PackageName, t : Time] : one Application {
	Device.apps.t & packageName.a
}

// This function returns a set of custom-permissions that are declared 
// before "app" is installed
fun customPermsBeforeAppInstallation[app : Application] : set Permission {
	// bAppT is the time before this app was installed
	let bAppT = min[app.(Device.apps)].prev {
		Device.customPerms.bAppT
	}
}

pred uninstall[t, t': Time, app: Application] {
	app in Device.apps.t // precondition
	Device.apps.t' = Device.apps.t - app	
	Device.customPerms.t' = Device.customPerms.t - app.declaredPerms.t

	all a : Application - app | grantPermissionsBroken[a, t, t']
	
	// Adjust permission groups
	all pg: Device.builtinPermGroups, p: Permission |
		p in pg.perms.t and p not in app.declaredPerms.t'
			=> p in pg.perms.t' else p not in pg.perms.t'
}

// Correct behavior for uninstall, not successfully implemented by Google though.
fun returnPermissionDataForUninstall[t: Time, app, appToBeRemoved: Application] : set PermissionData {
	{pd: app.permissionsState.t | pd.perm not in appToBeRemoved.declaredPerms.t}
}

pred update[t, t': Time, app: Application] {
	app in Device.apps.t // precondition
	Device.apps.t' = Device.apps.t
	
	// * app can change permission declarations. deal with permission declaration changes
	// * other apps' permissionsState can also change

	// 1. Fix custom permissions on the device
	Device.customPerms.t' =
		Device.customPerms.t - app.declaredPerms.t + app.declaredPerms.t'

	// 2. If any permission is removed from this app's manifest, update all other apps
	anyPermissionRemoved[t, t', app] => updatePermissionsForAllExcept[app, t, t']
		else
			all a : Application - app | a.permissionsState.t' = a.permissionsState.t

	// Regrant permissions for the current app
	grantPermissions[app, t, t']

	// Adjust permission groups
	all pg: Device.builtinPermGroups, p: Permission |
		(p in pg.perms.t and p not in (app.declaredPerms.t-app.declaredPerms.t'))
			or (p in app.declaredPerms.t' and p.permGroup = pg.name)
			=> p in pg.perms.t' else p not in pg.perms.t'
}

pred anyPermissionRemoved[t, t': Time, app: Application] {
	some p: app.declaredPerms.t | p not in app.declaredPerms.t'
}

pred updatePermissionsForAllExcept[appUpgraded: Application, t,t': Time] {
	all app: Device.apps.t - appUpgraded | grantPermissions[app, t, t']
}


fun findPermissionData[app: Application, p: Permission, t: Time] : one PermissionData {
	{pd: app.permissionsState.t | pd.perm = p}
}

// Correct behavior for uninstall, not successfully implemented by Google though.
fun returnPermissionData[t: Time, app: Application, p: Permission] : one PermissionData {
	{pd: app.permissionsState.t | pd.perm.name = p.name}
}

// In the initial state, no app is installed, and no custom-permission is defined
pred init[t: Time] {
	no Device.apps.t
	no Device.customPerms.t
	no Application.permissionsState.t
	//	all app: Application | app.targetSDK.t >= 23

	//system permission groups
	//some pg: PermissionGroup | pg in Device.builtinPermGroups
	//some p: Device.builtinPerms, pg: Device.builtinPermGroups | p in pg.perms.t
	ModelTracking.isUserPromptScreenShown.t = False
}

pred noChangesToAppsOrPermPrompt[t, t': Time, apps: set Application] {
	noChangesToAppManifests[t, t', apps]
	showPermissionPromptScreenNotExecuted[t, t']
}

pred noChangesToAppManifests[t, t': Time, apps: set Application] {
	all app: apps | noChangesToAppManifest[app, t, t']
}

// the trace constraint that form the states (install/unistall apps) into an execution trace
pred traces {
	init [first]
	all t: Time-last | let t' = t.next |
		some app: Application, c1, c2: Component |
			((install [t, t', app] or uninstall [t, t', app] or invoke[t, t', c1, c2])
				and noChangesToAppsOrPermPrompt[t, t', Application])
			or (update[t, t', app] and howAppShouldChange[t, t', app]
				and noChangesToAppsOrPermPrompt[t, t', Application-app])
			or (showPermissionPromptScreen[app, t, t'] and noChangesToAnyAppManifest[t, t'])

	all t: Time-last, p: Device.builtinPerms | let t' = t.next |
		p in Device.builtinPermGroups.perms.t <=> p in Device.builtinPermGroups.perms.t'
}
run traces for 7

pred showPermissionPromptScreen[app: Application, t, t': Time] {
	app in Device.apps.t
	app.targetSDK.t >= 23
	Device.customPerms.t' = Device.customPerms.t
	Device.apps.t' = Device.apps.t
	all a : Application - app | a.permissionsState.t = a.permissionsState.t'
	runAppToGrantDangerousRuntimePerms[app, t, t']
	all pd: app.permissionsState.t | pd in app.permissionsState.t'
	all pg: Device.builtinPermGroups, p: Permission |
		p in pg.perms.t => p in pg.perms.t' else p not in pg.perms.t'
}

pred showPermissionPromptScreenNotExecuted[t, t': Time] {
	ModelTracking.isUserPromptScreenShown.t' = ModelTracking.isUserPromptScreenShown.t
}

pred showPermissionPromptScreenExecuted[t, t': Time] {
	ModelTracking.isUserPromptScreenShown.t' != ModelTracking.isUserPromptScreenShown.t
}

pred runAppToGrantDangerousRuntimePerms[app: Application, t, t': Time] {
	showPermissionPromptScreenExecuted[t, t']
	all pname: app.usesPerms.t' | 
		hasPermissionData[pname, app, t] => (getPermissionData[pname, app, t] in app.permissionsState.t')
		else
			pname in (Device.builtinPerms + Device.customPerms.t').name => (
				let p = findPermissionByName[pname, t'] {
						p.protectionLevel = Dangerous => grantRuntimePermission[p, app, t']
						else
							no pd: PermissionData | pd.perm.name = pname and pd in app.permissionsState.t' 
				}
			) else
				no pd: PermissionData | pd.perm.name = pname and pd in app.permissionsState.t' 

	// permissions not requested by the app can never be granted
	no pd: app.permissionsState.t' | pd.perm.name not in app.usesPerms.t'
	//grantAllDangerousPermsInGroupIfOneGranted[app, t']
}

// Run the app to always grant runtime permissions...
pred runAppToGrantDangerousRuntimePermsOld[app: Application, t, t': Time] {
	showPermissionPromptScreenExecuted[t, t']
	all pname: app.usesPerms.t' | 
		pname in (Device.builtinPerms + Device.customPerms.t').name => (
			let p = findPermissionByName[pname, t'] {
					p.protectionLevel = Dangerous <=> grantRuntimePermission[p, app, t']
			}
		) else
			no pd: PermissionData | pd.perm.name = pname and pd in app.permissionsState.t' 
	
	// permissions not requested by the app can never be granted
	no pd: app.permissionsState.t' | pd.perm.name not in app.usesPerms.t'
	grantAllDangerousPermsInGroupIfOneGranted[app, t']
}

fact noTwoPermGroupsWithSameName {
	all disj pg1, pg2: PermissionGroup | pg1.name != pg2.name
}

////////////////////// PERMISSION GROUPS /////////////////////////////////////
// If one dangerous permission in a group is granted, all other dangerous perms will also be granted.
pred grantAllDangerousPermsInGroupIfOneGranted[app: Application, t: Time] {
	all p: app.permissionsState.t.perm |
		(p.permGroup in Device.builtinPermGroups.name and p.protectionLevel = Dangerous)
			=> 
			(let pg = getPermGroup[p.permGroup] {
					grantRuntimePermissionsOfGroup[pg, app, t]
				}
			)
}

fun getPermGroup[pgName: PermGroupName] : one PermissionGroup {
	{ pg: PermissionGroup | pg in Device.builtinPermGroups and pg.name = pgName }
}

pred grantRuntimePermissionsOfGroup[pg: PermissionGroup, app: Application, t: Time] {
all p: pg.perms.t | (p.protectionLevel = Dangerous and p.name in app.usesPerms.t)
									<=> grantRuntimePermission[p, app, t]
}

/////////////////////////////////////////////////////////////////////////////////////////////////

pred noChangesToAnyAppManifest[t, t': Time] {
	all app: Application | noChangesToAppManifest[app, t, t']
}

pred howAppShouldChange[t, t': Time, app: Application] {
	app.targetSDK.t' = app.targetSDK.t

	// In order not to invoke grantPermissions unnecessarily, do not let an app declare
	// a different permission that looks exactly like a permission defined by this app before
	no disj p1, p2: Permission |
		p1 in app.declaredPerms.t and p2 in app.declaredPerms.t'
			and p1.name = p2.name and p1.protectionLevel = p2.protectionLevel
}

pred noChanges[t, t': Time] {
	Device.customPerms.t' = Device.customPerms.t
	Device.apps.t' = Device.apps.t
	all a : Application | a.permissionsState.t' = a.permissionsState.t
}

pred invoke[t, t' : Time, caller, callee: Component]{
	caller.app + callee.app in Device.apps.t
	// call succeeds only if caller has "uses-permission" for the permission guarding the provider
	canCall[caller, callee, t]
	//canCallCusper[caller, callee, t]
	// nothing changes
	noChanges[t, t']
}

fun guardedBy : Component -> PermName {
	{c: Component, p: Name |
		// component-specific permission takes priority over the app-wide permission
    	// http://developer.android.com/guide/topics/manifest/application-element.html#prmsn
		(p = c.guard.name) or
		(no c.guard and p = c.app.guard.name)
	}
}

fun getSourceId[c: Component, t: Time] : one AppSignature {
	{p: AppSignature |
		// component-specific permission takes priority over the app-wide permission
    	// http://developer.android.com/guide/topics/manifest/application-element.html#prmsn
		(p = findPermissionByName[c.guard.name, t].sourceId)
		or
		(no c.guard and p = findPermissionByName[c.app.guard.name, t].sourceId)
	}
}


// How permission enforcement was done before Cusper
pred canCall[caller, callee: Component, t : Time] {
	// the permission required to access the callee is one of the caller's uses-permissions
	guardedBy[callee] in caller.app.permissionsState.t.perm.name
}

pred canCallFixed[caller, callee: Component, t : Time] {
	// the permission required to access the callee is one of the caller's uses-permissions
	let pname = guardedBy[callee], p = findPermissionByName[pname, t] {
		p in caller.app.permissionsState.t.perm
	}
}

fun getPermissionData[pname: PermName, app: Application, t: Time] : one PermissionData {
	{pd: PermissionData | pd in app.permissionsState.t and pd.perm.name = pname}
}

pred canCallCusper[caller, callee: Component, t : Time] {
	// why wrong: we need the permission that was on the system when callee app was installed
	// not the one on the system when invocation occurred.
		let pname = guardedBy[callee],
		source = getSourceId[callee, t], // name translation during enforcement for components
		pd = getPermissionData[pname, caller.app, t] {
			pname in pd.perm.name
			source in pd.perm.sourceId
		}
}

// Logically the correct one! It checks if the permission granted is EXACTLY the one used.
// However, the system currently performs the checks based on only the names.
pred authorizedOld[caller, provider: Component, t:Time] {
	let pname = guardedBy[provider], 
		grantedPermission = { p:  caller.app.permissionsState.t.perm | p.name = pname}, 
		requiredPermission = { p: (provider.app.declaredPerms.t + Device.builtinPerms) | p.name = pname } |
				grantedPermission = requiredPermission
}

// But the correct one messes up things since apps can update their definitions
// and redefine permissions w/ same name but different protection level etc.
// For unauthorized use assertion, cases where app isn't authorized to access its own component 
// (since it updated the definition and component is protected with the old permission) appears
// also the repackaged app case comes up too.
pred authorized[caller, provider: Component, t:Time] {
	let pname = guardedBy[provider], 
		grantedPermission = { p:  caller.app.permissionsState.t.perm | p.name = pname}, 
		requiredPermission = { p: (provider.app.declaredPerms.t + Device.builtinPerms) | p.name = pname }
		{
				grantedPermission.name = requiredPermission.name
				// Proper enforcement should also check the source of a permission
				grantedPermission.sourceId = requiredPermission.sourceId
		}
}

fact NoRepackagedApps {
	no disj app1, app2: Application | app1.packageName = app2.packageName
}

/******************************************************************************
*********** Android Runtime Permission Model Operations ************ 
*******************************************************************************/
pred clearPermissionFlags[pd: PermissionData, t: Time] {
	pd.flags.FLAG_PERMISSION_REVOKE_ON_UPGRADE = False
	pd.flags.FLAG_PERMISSION_GRANTED_BY_DEFAULT = False
	pd.flags.FLAG_PERMISSION_SYSTEM_FIXED = False
	pd.flags.FLAG_PERMISSION_POLICY_FIXED = False
}

pred setPermissionFlags[pd: PermissionData, t: Time] {
	pd.flags.FLAG_PERMISSION_REVOKE_ON_UPGRADE = True
	pd.flags.FLAG_PERMISSION_GRANTED_BY_DEFAULT = True
	pd.flags.FLAG_PERMISSION_SYSTEM_FIXED = True
	pd.flags.FLAG_PERMISSION_POLICY_FIXED = True
}

// Basic grant and revoke operations
pred revokeInstallPermission[p: Permission, app : Application, t, t' : Time] {
	no pd: app.permissionsState.t' | pd.perm.name = p.name and pd.isRuntime = False
}

pred revokeRuntimePermission[p: Permission, app : Application, t, t' : Time] {
	no pd: app.permissionsState.t' | pd.perm.name = p.name and pd.isRuntime = True
}

pred grantInstallPermission[p: Permission, app : Application, t, t' : Time] {
	one pd: app.permissionsState.t' |
		pd.perm = p and pd.isRuntime = False		
}

// Corrected version of grant install permission case according to Cusper
pred grantInstallPermissionCusper[p: Permission, app : Application, t, t' : Time] {
	one pd: app.permissionsState.t' |
		pd.perm = p and pd.isRuntime = False
			// Fix to update custom permission upgrade vilnerability
			and (p.isCustomPermission = False => clearPermissionFlags[pd, t'] else setPermissionFlags[pd, t'])
}

pred grantRuntimePermission[p: Permission, app : Application, t' : Time] {
	one pd: app.permissionsState.t' | pd.perm = p and pd.isRuntime = True
}

// Cases in the grantPermissionsLPw method in AOSP
pred grantInstallCase[p: Permission, app : Application, t, t' : Time] {
	hasRuntimePermission[p, app, t] => revokeRuntimePermission[p, app, t, t']
	
	grantInstallPermission[p, app, t, t']
	//grantInstallPermissionCusper[p, app, t, t']
	
	// no runtime permission should exist for this permission
	no pd2: app.permissionsState.t' | pd2.perm = p and pd2.isRuntime = True
}

pred grantInstallLegacyCase[p: Permission, app : Application, t, t' : Time] {
	grantInstallPermission[p, app, t, t']
	//grantInstallPermissionCusper[p, app, t, t']

	// no runtime permission should exist for this permission
	no pd2: app.permissionsState.t' | pd2.perm = p and pd2.isRuntime = True
}

pred grantRuntimeCase[p: Permission, app : Application, t, t' : Time] {
	hasRuntimePermission[p, app, t] <=> grantRuntimePermission[p, app, t']
	
	// no install permission should exist for this permission
	no pd2: app.permissionsState.t' | pd2.perm = p and pd2.isRuntime = False
}

pred grantUpgradeCase[p: Permission, app : Application, t, t' : Time] {
	// if permission was previously granted as install, revoke it
	hasInstallPermission[p, app, t] => revokeInstallPermission[p, app, t, t']

	// Runtime permission will be granted only if it wasn't manually revoked by the user
	hasInstallPermission[p, app, t] and 
		returnPermissionData[t, app, p].flags.FLAG_PERMISSION_REVOKE_ON_UPGRADE = False
			<=> grantRuntimePermission[p, app, t']
}

pred denyPermissionCase[p :  Permission, app : Application, t, t' : Time] {
	hasInstallPermission[p, app, t] => revokeInstallPermission[p, app, t, t']
}

pred hasInstallPermission[p : Permission, app : Application, t :  Time] {
	one pd: app.permissionsState.t | pd.perm.name = p.name and pd.isRuntime = False
}

pred hasRuntimePermission[p : Permission, app : Application, t :  Time] {
	one pd: app.permissionsState.t | pd.perm.name = p.name and pd.isRuntime = True
}

// update flags for t'
pred updatePermissionFlags[p :  Permission, app : Application, t : Time] {
	one pd : app.permissionsState.t | pd.perm = p implies
		pd.flags.FLAG_PERMISSION_REVOKE_ON_UPGRADE = False
}

pred hasPermissionData[pname: PermName, app: Application, t: Time] {
	one pd: app.permissionsState.t | pd.perm.name = pname
}

pred grantPermissions[app : Application, t, t' : Time] {
	grantRuntimeModel[app, t, t']
	app.permissionsState.t'.perm in Device.customPerms.t' + Device.builtinPerms //+ app.declaredPerms
}

pred grantRuntimeModel[app: Application, t, t': Time] {
	all pname: app.usesPerms.t' | 
		pname in (Device.builtinPerms + Device.customPerms.t').name => (
			let p = findPermissionByName[pname, t'] {
				p.protectionLevel = Normal => grantInstallCase[p, app, t, t']
				else
					(p.protectionLevel = Dangerous and app.targetSDK.t' >= 23 and hasInstallPermission[p, app, t])
						=> grantUpgradeCase[p, app, t, t']
					else
						(p.protectionLevel = Dangerous and app.targetSDK.t' >= 23 and not hasInstallPermission[p, app, t])
							=> grantRuntimeCase[p, app, t, t']
						else
							(p.protectionLevel = Dangerous and app.targetSDK.t' < 23)
								=> grantInstallLegacyCase[p, app, t, t']
							else
								p.protectionLevel = Signature and (verifySignatureForCustomPermission[p, app, t'] 
								or verifySignatureForBuiltinPermission[p, app]) 
								=> grantInstallCase[p, app, t, t']
								else //deny permission
									no pd: PermissionData | pd.perm.name = pname and pd in app.permissionsState.t'
			}
		)
		else // permission doesnt exist, basically the null case of bp ("continue") 
			// in order to show the vulnerability, we need to assign a pd to permissionsState for time t'
			// if there was one for time t. (copy it over basically)
			let pd = getPermissionData[pname, app, t]{
				hasPermissionData[pname, app, t] and pd.isRuntime = True and pd.perm.protectionLevel = Dangerous =>
					pd in app.permissionsState.t'
				else
					no pd: PermissionData | pd.perm.name = pname and pd in app.permissionsState.t' 
			}
	// make sure app cannot be granted a permission that it doesn't request
	no pd: app.permissionsState.t' | pd.perm.name not in app.usesPerms.t'
}

// It is necessary to allow the app to have a permission that was defined in t but not t',
// in order to be able to observe the confused deput attack.
// This is necessary for uninstallation only.
pred grantPermissionsBroken[app : Application, t, t' : Time] {
	grantRuntimeModel[app, t, t']
	app.permissionsState.t'.perm in Device.customPerms.t + Device.builtinPerms + app.declaredPerms.t'
}

/******************************************************************************
*********** Assertions for fundamental security properties ************ 
*******************************************************************************/

// One component can call another only if it's authorized to do so.
// This assertion is violated by the original model but satisfied with Cusper.
assert NoUnauthorizedAccess {
	traces implies 
		all t : Time - last, caller, callee : Component | 		
			invoke[t, t.next, caller, callee] implies authorized[caller, callee, t]
}
// It takes 7 time steps in our model to recreate the confused deputy vulnerability.
check NoUnauthorizedAccess for 7 but exactly 7 Time, 3 Application, 2 Permission, 2 Component, 1 PermissionData, 6 Int
check NoUnauthorizedAccess for 7 but exactly 3 Application, 2 Component, 3 Permission, 6 Int

assert NoDangerousPermGrantedRuntimeWithoutConsent {
	traces implies
		all t: Time-last | let t' = t.next |
			showPermissionPromptScreenNotExecuted[t, t']
				implies
					no p: Permission |
					//no p: Device.builtinPerms |
						p in getAllGrantedDangerousRuntimePerms[t']
							and p not in getAllGrantedDangerousRuntimePerms[t]
}

check NoDangerousPermGrantedRuntimeWithoutConsent for 3 but exactly 1 Application, 1 Component, 3 Permission, 4 Name, 6 Int
check NoDangerousPermGrantedRuntimeWithoutConsent for 3 but 6 Int// but exactly 4 Name

// Protection level dangerous indicates permission is runtime for apps >= 23
// Returns all the runtime permissions granted to apps on device
fun getAllGrantedDangerousRuntimePerms[t: Time] : set Permission {
	{p : Permission | p.protectionLevel = Dangerous and p in getNewAppsOnDevice[t].permissionsState.t.perm}
}

// Returns apps w/ SDK >= 23
fun getNewAppsOnDevice[t: Time] : set Application {
	{app: Device.apps.t | app.targetSDK.t >= 23}
}

// App 2 that is not signed with the certificate of App 1 cannot use (be granted) 
// App 1's signature permissions
assert NoUnauthorizedUseOfCustomSignaturePermission {
	traces implies
		all t : Time - last, p: Permission, disj app1, app2: Application |
			app1 in Device.apps.t and app2 in Device.apps.t 
			and p in app1.declaredPerms.t and p not in app2.declaredPerms.t
			and p.protectionLevel = Signature and app1.signature != app2.signature
				implies p.name not in app2.permissionsState.t.perm.name		
}
check  NoUnauthorizedUseOfCustomSignaturePermission for 6 but exactly 7 Time, 3 Application, 2 Permission, 2 Component, 1 PermissionData

assert NoUnauthorizedUseOfBuiltinSignaturePermission {
	traces implies
		all t : Time - last, p: Permission, app: Application |
			app in Device.apps.t
			and app.signature != Device.platformSignature
			and p in Device.builtinPerms
			and p.protectionLevel = Signature
				implies p.name not in app.permissionsState.t.perm.name		
}
check  NoUnauthorizedUseOfBuiltinSignaturePermission for 7 but exactly 7 Time, 3 Application, 2 Permission, 2 Component, 1 PermissionData

// two apps that are not signed with the same signature cannot declare a permission
// with the same name as the other app's declared permission
assert UniquePermissionName {
	traces implies 
		all t : Time - last,  p1, p2: Permission, app1, app2 : Application | 
			app1 in Device.apps.t and app2 in Device.apps.t
			and (p1 in app1.declaredPerms.t) and (p2 in app2.declaredPerms.t)
			and app1.signature != app2.signature
				implies p1.name != p2.name
}
check UniquePermissionName

// App 2 that is not signed with the certificate of App 1 cannot use (be granted) 
// App 1's signature permissions
assert NoUnauthorizedUseOfSignaturePermission {
	traces implies
		all t : Time - last, p: Permission, app1, app2: Application |
			app1 in Device.apps.t and app2 in Device.apps.t 
			and p in app1.declaredPerms.t and p not in app2.declaredPerms.t
			and p.protectionLevel = Signature and app1.signature != app2.signature
				implies p.name not in app2.permissionsState.t.perm.name
}
check NoUnauthorizedUseOfSignaturePermission for 7 but exactly 7 Time, 3 Application, 2 Permission, 2 Component, 1 PermissionData


assert NoNonExistentPermissionIsGranted {
	traces implies
		all t: Time - last, p: Permission, app: Application |
			app in Device.apps.t and p in app.permissionsState.t.perm
				implies  p in Device.customPerms.t or p in Device.builtinPerms
}
check NoNonExistentPermissionIsGranted for 5


pred allRequestedDangerousPermsOfGroupGranted[pg: PermissionGroup, app: Application, t: Time] {
	all p: pg.perms.t |
		p.protectionLevel = Dangerous and p.name in app.usesPerms.t
			=> p in app.permissionsState.t.perm
}

assert GroupGrantingOfDangerousPermsWorks {
	traces implies
		all t: Time-last, app: Device.apps.t, p: Permission, pg: Device.builtinPermGroups |
			app.targetSDK.t >= 23 and
				p.protectionLevel = Dangerous and p.permGroup = pg.name and
					p in app.permissionsState.t.perm
						=> allRequestedDangerousPermsOfGroupGranted[pg, app, t]
}
check GroupGrantingOfDangerousPermsWorks

